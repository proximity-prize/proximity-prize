import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0648
import ProximityPrize.SubmissionLower.Z6969Pack0649
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

set_option Elab.async false

-- merged module Z6969Pack0653
section Merged_Z6969Pack0653

-- Source: Research6969.TerminalRanks52To55
section Z6969Source0906
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks52To55
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3628_775 : P1_7_1.groupedPoleMoment 3628 775 ≤ 4707932919737 :=
  _root_.PoleAffine6970.certified 3628 775 4707932919737 (by decide) (by decide +kernel)

theorem moment3628_793 : P1_7_1.groupedPoleMoment 3628 793 ≤ 4792991160379 :=
  _root_.PoleAffine6970.certified 3628 793 4792991160379 (by decide) (by decide +kernel)

theorem moment3628_819 : P1_7_1.groupedPoleMoment 3628 819 ≤ 4914696693929 :=
  _root_.PoleAffine6970.certified 3628 819 4914696693929 (by decide) (by decide +kernel)

theorem moment3798_830 : P1_7_1.groupedPoleMoment 3798 830 ≤ 5755034811151 :=
  _root_.PoleAffine6970.certified 3798 830 5755034811151 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks52To55

namespace Research6969.PackedRanks.TerminalRanks52To55
open Research6969.TerminalAuxBanks
theorem rank52 (u:ℕ) : P3_7_1.BankOK (bank52 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank52 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank52 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank52 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank52 u).shape=523640687820800; omega, moment3628_775,by change 3628<K1.p;decide⟩
theorem rank53 (u:ℕ) : P3_7_1.BankOK (bank53 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank53 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank53 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank53 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank53 u).shape=532875289296896; omega, moment3628_793,by change 3628<K1.p;decide⟩
theorem rank54 (u:ℕ) : P3_7_1.BankOK (bank54 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank54 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank54 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank54 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank54 u).shape=546063062138880; omega, moment3628_819,by change 3628<K1.p;decide⟩
theorem rank55 (u:ℕ) : P3_7_1.BankOK (bank55 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank55 u).shape (by change 2*830≤2730;decide) (by change 2730+830≤3798+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2730-2*830) 830=6*615323551662080:=by decide
  change 6*P1_7_1.nodeRows (bank55 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank55 u).shape=262144*P1_7_1_2.sixPerNode (2730-2*830) 830 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank55 u).shape=615323551662080; omega, moment3798_830,by change 3798<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks52To55
end Z6969Source0906

-- Source: Research6969.OrdSource03
section Z6969Source0907
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src48:PhysicalWindow.Request := ⟨⟨⟨2600,3628,793,45124⟩,532875289296896,4792991160379⟩,15,2,1,302619,25⟩
private theorem shift48_2314 : (PhysicalWindow.Triangular src48) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift48_2317 : (PhysicalWindow.Triangular src48) 2317 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift48_2326 : (PhysicalWindow.Triangular src48) 2326 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift48_2351 : (PhysicalWindow.Triangular src48) 2351 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover48 : PhysicalWindow.Cover (PhysicalWindow.Triangular src48) 2411 2314 [2316, 2325, 2350, 2411] := by
  exact ⟨by decide, by decide, shift48_2314, by decide, by decide, shift48_2317, by decide, by decide, shift48_2326, by decide, by decide, shift48_2351, rfl⟩
def row48:OrdinaryBounds.Source 2314 2411:=
  ⟨src48,⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover48⟩⟩
private def src49:PhysicalWindow.Request := ⟨⟨⟨2800,3907,854,130242⟩,665461916958720,6445344460182⟩,22,3,1,385979,10⟩
private theorem shift49_2314 : (PhysicalWindow.Triangular src49) 2314 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift49_2316 : (PhysicalWindow.Triangular src49) 2316 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift49_2322 : (PhysicalWindow.Triangular src49) 2322 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift49_2339 : (PhysicalWindow.Triangular src49) 2339 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift49_2386 : (PhysicalWindow.Triangular src49) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover49 : PhysicalWindow.Cover (PhysicalWindow.Triangular src49) 2411 2314 [2315, 2321, 2338, 2385, 2411] := by
  exact ⟨by decide, by decide, shift49_2314, by decide, by decide, shift49_2316, by decide, by decide, shift49_2322, by decide, by decide, shift49_2339, by decide, by decide, shift49_2386, rfl⟩
def row49:OrdinaryBounds.Source 2314 2411:=
  ⟨src49,⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 130242, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover49⟩⟩
private def src50:PhysicalWindow.Request := ⟨⟨⟨2600,3628,793,115771⟩,532875289296896,4792991160379⟩,22,3,1,385979,13⟩
private theorem shift50_2314 : (PhysicalWindow.Triangular src50) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift50_2319 : (PhysicalWindow.Triangular src50) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift50_2333 : (PhysicalWindow.Triangular src50) 2333 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift50_2372 : (PhysicalWindow.Triangular src50) 2372 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover50 : PhysicalWindow.Cover (PhysicalWindow.Triangular src50) 2411 2314 [2318, 2332, 2371, 2411] := by
  exact ⟨by decide, by decide, shift50_2314, by decide, by decide, shift50_2319, by decide, by decide, shift50_2333, by decide, by decide, shift50_2372, rfl⟩
def row50:OrdinaryBounds.Source 2314 2411:=
  ⟨src50,⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 115771, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover50⟩⟩
private def src51:PhysicalWindow.Request := ⟨⟨⟨2600,3628,793,102908⟩,532875289296896,4792991160379⟩,22,3,1,385979,15⟩
private theorem shift51_2314 : (PhysicalWindow.Triangular src51) 2314 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift51_2323 : (PhysicalWindow.Triangular src51) 2323 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift51_2348 : (PhysicalWindow.Triangular src51) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover51 : PhysicalWindow.Cover (PhysicalWindow.Triangular src51) 2411 2314 [2322, 2347, 2411] := by
  exact ⟨by decide, by decide, shift51_2314, by decide, by decide, shift51_2323, by decide, by decide, shift51_2348, rfl⟩
def row51:OrdinaryBounds.Source 2314 2411:=
  ⟨src51,⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 102908, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover51⟩⟩
private def src52:PhysicalWindow.Request := ⟨⟨⟨2600,3628,793,81311⟩,532875289296896,4792991160379⟩,22,3,1,385979,17⟩
private theorem shift52_2314 : (PhysicalWindow.Triangular src52) 2314 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift52_2316 : (PhysicalWindow.Triangular src52) 2316 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift52_2322 : (PhysicalWindow.Triangular src52) 2322 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift52_2339 : (PhysicalWindow.Triangular src52) 2339 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift52_2386 : (PhysicalWindow.Triangular src52) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover52 : PhysicalWindow.Cover (PhysicalWindow.Triangular src52) 2411 2314 [2315, 2321, 2338, 2385, 2411] := by
  exact ⟨by decide, by decide, shift52_2314, by decide, by decide, shift52_2316, by decide, by decide, shift52_2322, by decide, by decide, shift52_2339, by decide, by decide, shift52_2386, rfl⟩
def row52:OrdinaryBounds.Source 2314 2411:=
  ⟨src52,⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 81311, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover52⟩⟩
private def src53:PhysicalWindow.Request := ⟨⟨⟨2800,3907,854,72277⟩,665461916958720,6445344460182⟩,22,3,1,385979,18⟩
private theorem shift53_2314 : (PhysicalWindow.Triangular src53) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift53_2319 : (PhysicalWindow.Triangular src53) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift53_2333 : (PhysicalWindow.Triangular src53) 2333 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift53_2372 : (PhysicalWindow.Triangular src53) 2372 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover53 : PhysicalWindow.Cover (PhysicalWindow.Triangular src53) 2411 2314 [2318, 2332, 2371, 2411] := by
  exact ⟨by decide, by decide, shift53_2314, by decide, by decide, shift53_2319, by decide, by decide, shift53_2333, by decide, by decide, shift53_2372, rfl⟩
def row53:OrdinaryBounds.Source 2314 2411:=
  ⟨src53,⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 72277, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover53⟩⟩
private def src54:PhysicalWindow.Request := ⟨⟨⟨2600,3628,793,57109⟩,532875289296896,4792991160379⟩,22,3,1,385979,21⟩
private theorem shift54_2314 : (PhysicalWindow.Triangular src54) 2314 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift54_2323 : (PhysicalWindow.Triangular src54) 2323 2348 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift54_2349 : (PhysicalWindow.Triangular src54) 2349 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover54 : PhysicalWindow.Cover (PhysicalWindow.Triangular src54) 2411 2314 [2322, 2348, 2411] := by
  exact ⟨by decide, by decide, shift54_2314, by decide, by decide, shift54_2323, by decide, by decide, shift54_2349, rfl⟩
def row54:OrdinaryBounds.Source 2314 2411:=
  ⟨src54,⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover54⟩⟩
private def src55:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,64247⟩,665461916958720,6440035562832⟩,32,3,1,385979,24⟩
private theorem shift55_2314 : (PhysicalWindow.Triangular src55) 2314 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift55_2325 : (PhysicalWindow.Triangular src55) 2325 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift55_2356 : (PhysicalWindow.Triangular src55) 2356 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover55 : PhysicalWindow.Cover (PhysicalWindow.Triangular src55) 2411 2314 [2324, 2355, 2411] := by
  exact ⟨by decide, by decide, shift55_2314, by decide, by decide, shift55_2325, by decide, by decide, shift55_2356, rfl⟩
def row55:OrdinaryBounds.Source 2314 2411:=
  ⟨src55,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover55⟩⟩
private def src56:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,40111⟩,665461916958720,6440035562832⟩,32,3,1,385979,27⟩
private theorem shift56_2314 : (PhysicalWindow.Triangular src56) 2314 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift56_2322 : (PhysicalWindow.Triangular src56) 2322 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift56_2344 : (PhysicalWindow.Triangular src56) 2344 2405 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift56_2406 : (PhysicalWindow.Triangular src56) 2406 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover56 : PhysicalWindow.Cover (PhysicalWindow.Triangular src56) 2411 2314 [2321, 2343, 2405, 2411] := by
  exact ⟨by decide, by decide, shift56_2314, by decide, by decide, shift56_2322, by decide, by decide, shift56_2344, by decide, by decide, shift56_2406, rfl⟩
def row56:OrdinaryBounds.Source 2314 2411:=
  ⟨src56,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 40111, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover56⟩⟩
private def src57:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,35655⟩,665461916958720,6440035562832⟩,45,3,1,385979,32⟩
private theorem shift57_2314 : (PhysicalWindow.Triangular src57) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift57_2320 : (PhysicalWindow.Triangular src57) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift57_2337 : (PhysicalWindow.Triangular src57) 2337 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift57_2385 : (PhysicalWindow.Triangular src57) 2385 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover57 : PhysicalWindow.Cover (PhysicalWindow.Triangular src57) 2411 2314 [2319, 2336, 2384, 2411] := by
  exact ⟨by decide, by decide, shift57_2314, by decide, by decide, shift57_2320, by decide, by decide, shift57_2337, by decide, by decide, shift57_2385, rfl⟩
def row57:OrdinaryBounds.Source 2314 2411:=
  ⟨src57,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover57⟩⟩
private def src58:PhysicalWindow.Request := ⟨⟨⟨2300,3208,724,28173⟩,377903408742400,3004743122568⟩,45,3,1,385979,36⟩
private theorem shift58_2314 : (PhysicalWindow.Triangular src58) 2314 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift58_2324 : (PhysicalWindow.Triangular src58) 2324 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift58_2352 : (PhysicalWindow.Triangular src58) 2352 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover58 : PhysicalWindow.Cover (PhysicalWindow.Triangular src58) 2411 2314 [2323, 2351, 2411] := by
  exact ⟨by decide, by decide, shift58_2314, by decide, by decide, shift58_2324, by decide, by decide, shift58_2352, rfl⟩
def row58:OrdinaryBounds.Source 2314 2411:=
  ⟨src58,⟨Research6969.PackedRanks.TerminalRanks32To35.rank34 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover58⟩⟩
private def src59:PhysicalWindow.Request := ⟨⟨⟨2600,3626,793,28173⟩,532875289296896,4784491173220⟩,63,3,1,385979,42⟩
private theorem shift59_2314 : (PhysicalWindow.Triangular src59) 2314 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift59_2325 : (PhysicalWindow.Triangular src59) 2325 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift59_2356 : (PhysicalWindow.Triangular src59) 2356 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover59 : PhysicalWindow.Cover (PhysicalWindow.Triangular src59) 2411 2314 [2324, 2355, 2411] := by
  exact ⟨by decide, by decide, shift59_2314, by decide, by decide, shift59_2325, by decide, by decide, shift59_2356, rfl⟩
def row59:OrdinaryBounds.Source 2314 2411:=
  ⟨src59,⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover59⟩⟩
private def src60:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,31694⟩,665461916958720,6434729640882⟩,85,3,1,385979,48⟩
private theorem shift60_2314 : (PhysicalWindow.Triangular src60) 2314 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift60_2321 : (PhysicalWindow.Triangular src60) 2321 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift60_2341 : (PhysicalWindow.Triangular src60) 2341 2396 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift60_2397 : (PhysicalWindow.Triangular src60) 2397 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover60 : PhysicalWindow.Cover (PhysicalWindow.Triangular src60) 2411 2314 [2320, 2340, 2396, 2411] := by
  exact ⟨by decide, by decide, shift60_2314, by decide, by decide, shift60_2321, by decide, by decide, shift60_2341, by decide, by decide, shift60_2397, rfl⟩
def row60:OrdinaryBounds.Source 2314 2411:=
  ⟨src60,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover60⟩⟩
def row61:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1146,⟨Research6969.PackedRanks.TerminalRanks16To19.rank19 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1146⟩⟩
private def src62:PhysicalWindow.Request := ⟨⟨⟨2800,3903,854,31694⟩,665461916958720,6424126719762⟩,115,3,1,385979,65⟩
private theorem shift62_2314 : (PhysicalWindow.Triangular src62) 2314 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift62_2329 : (PhysicalWindow.Triangular src62) 2329 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift62_2372 : (PhysicalWindow.Triangular src62) 2372 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover62 : PhysicalWindow.Cover (PhysicalWindow.Triangular src62) 2411 2314 [2328, 2371, 2411] := by
  exact ⟨by decide, by decide, shift62_2314, by decide, by decide, shift62_2329, by decide, by decide, shift62_2372, rfl⟩
def row62:OrdinaryBounds.Source 2314 2411:=
  ⟨src62,⟨Research6969.PackedRanks.TerminalRanks64To67.rank64 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover62⟩⟩
def row63:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1148,⟨Research6969.PackedRanks.TerminalRanks16To19.rank18 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1148⟩⟩
end Research6969.OrdSource
end Z6969Source0907

-- Source: Research6969.PhysicalChecks018
section Z6969Source0908
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1160 : Request := ⟨⟨⟨2800,3896,812,153803⟩,640331821875200,6140432144913⟩,325,3,1,385979,4097⟩
theorem cover1160 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1160) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1161 : Request := ⟨⟨⟨2800,3896,812,157727⟩,640331821875200,6140432144913⟩,325,3,1,385979,4097⟩
theorem cover1161 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1161) 2411 2314 [2318, 2333, 2377, 2411] := triangleCover (by decide +kernel)
def src1162 : Request := ⟨⟨⟨2000,2782,610,175105⟩,242679148707840,1662397981334⟩,250,3,1,385979,8193⟩
theorem cover1162 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1162) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1163 : Request := ⟨⟨⟨1200,1669,366,119707⟩,52501327642624,215795999824⟩,150,3,1,385979,32769⟩
theorem cover1163 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1163) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1215 : Request := ⟨⟨⟨2800,3906,854,128107⟩,665461916958720,6440035562832⟩,45,4,1,514639,1⟩
theorem cover1215 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1215) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1216 : Request := ⟨⟨⟨2600,3626,793,475797⟩,532875289296896,4784491173220⟩,63,4,1,514639,1⟩
theorem cover1216 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1216) 2411 2314 [2321, 2343, 2405, 2411] := triangleCover (by decide +kernel)
def src1226 : Request := ⟨⟨⟨2300,3209,702,91364⟩,369170633195520,2936492475204⟩,32,4,1,514639,2⟩
theorem cover1226 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1226) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1228 : Request := ⟨⟨⟨2600,3626,793,422931⟩,532875289296896,4784491173220⟩,63,4,1,514639,2⟩
theorem cover1228 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1228) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1237 : Request := ⟨⟨⟨2800,3906,854,115558⟩,665461916958720,6440035562832⟩,45,4,1,514639,4⟩
theorem cover1237 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1237) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1239 : Request := ⟨⟨⟨2600,3626,775,530820⟩,523640687820800,4699589564453⟩,63,4,1,514639,4⟩
theorem cover1239 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1239) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src1251 : Request := ⟨⟨⟨2600,3627,793,101341⟩,532875289296896,4788739883894⟩,45,4,1,514639,9⟩
theorem cover1251 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1251) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1252 : Request := ⟨⟨⟨2600,3626,775,422931⟩,523640687820800,4699589564453⟩,63,4,1,514639,9⟩
theorem cover1252 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1252) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1256 : Request := ⟨⟨⟨2800,3906,854,79138⟩,665461916958720,6440035562832⟩,45,4,1,514639,13⟩
theorem cover1256 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1256) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1257 : Request := ⟨⟨⟨2600,3626,775,375939⟩,523640687820800,4699589564453⟩,63,4,1,514639,13⟩
theorem cover1257 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1257) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1268 : Request := ⟨⟨⟨2800,3906,854,63700⟩,665461916958720,6440035562832⟩,45,4,1,514639,17⟩
theorem cover1268 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1268) 2411 2314 [2314, 2317, 2325, 2347, 2409, 2411] := triangleCover (by decide +kernel)
def src1269 : Request := ⟨⟨⟨2600,3626,775,297039⟩,523640687820800,4699589564453⟩,63,4,1,514639,17⟩
theorem cover1269 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1269) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0908

-- Source: Research6969.TerminalRanks8To11
section Z6969Source0909
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks8To11
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment2435_522 : P1_7_1.groupedPoleMoment 2435 522 ≤ 959076692411 :=
  _root_.PoleAffine6970.certified 2435 522 959076692411 (by decide) (by decide +kernel)

theorem moment2437_551 : P1_7_1.groupedPoleMoment 2437 551 ≤ 1002904994165 :=
  _root_.PoleAffine6970.certified 2437 551 1002904994165 (by decide) (by decide +kernel)

theorem moment2438_534 : P1_7_1.groupedPoleMoment 2438 534 ≤ 980085107193 :=
  _root_.PoleAffine6970.certified 2438 534 980085107193 (by decide) (by decide +kernel)

theorem moment2438_551 : P1_7_1.groupedPoleMoment 2438 551 ≤ 1004231319985 :=
  _root_.PoleAffine6970.certified 2438 551 1004231319985 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks8To11

namespace Research6969.PackedRanks.TerminalRanks8To11
open Research6969.TerminalAuxBanks
theorem rank8 (u:ℕ) : P3_7_1.BankOK (bank8 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank8 u).shape (by change 2*522≤1750;decide) (by change 1750+522≤2435+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1750-2*522) 522=6*159899889172480:=by decide
  change 6*P1_7_1.nodeRows (bank8 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank8 u).shape=262144*P1_7_1_2.sixPerNode (1750-2*522) 522 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank8 u).shape=159899889172480; omega, moment2435_522,by change 2435<K1.p;decide⟩
theorem rank9 (u:ℕ) : P3_7_1.BankOK (bank9 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank9 u).shape (by change 2*551≤1750;decide) (by change 1750+551≤2437+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1750-2*551) 551=6*166595992223744:=by decide
  change 6*P1_7_1.nodeRows (bank9 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank9 u).shape=262144*P1_7_1_2.sixPerNode (1750-2*551) 551 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank9 u).shape=166595992223744; omega, moment2437_551,by change 2437<K1.p;decide⟩
theorem rank10 (u:ℕ) : P3_7_1.BankOK (bank10 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank10 u).shape (by change 2*534≤1750;decide) (by change 1750+534≤2438+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1750-2*534) 534=6*162688810352640:=by decide
  change 6*P1_7_1.nodeRows (bank10 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank10 u).shape=262144*P1_7_1_2.sixPerNode (1750-2*534) 534 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank10 u).shape=162688810352640; omega, moment2438_534,by change 2438<K1.p;decide⟩
theorem rank11 (u:ℕ) : P3_7_1.BankOK (bank11 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank11 u).shape (by change 2*551≤1750;decide) (by change 1750+551≤2438+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1750-2*551) 551=6*166595992223744:=by decide
  change 6*P1_7_1.nodeRows (bank11 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank11 u).shape=262144*P1_7_1_2.sixPerNode (1750-2*551) 551 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank11 u).shape=166595992223744; omega, moment2438_551,by change 2438<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks8To11
end Z6969Source0909

-- Source: Research6969.OrdSource04
section Z6969Source0910
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src64:PhysicalWindow.Request := ⟨⟨⟨2600,3623,819,35655⟩,546063062138880,4892906717079⟩,150,3,1,385979,97⟩
private theorem shift64_2314 : (PhysicalWindow.Triangular src64) 2314 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift64_2323 : (PhysicalWindow.Triangular src64) 2323 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift64_2348 : (PhysicalWindow.Triangular src64) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover64 : PhysicalWindow.Cover (PhysicalWindow.Triangular src64) 2411 2314 [2322, 2347, 2411] := by
  exact ⟨by decide, by decide, shift64_2314, by decide, by decide, shift64_2323, by decide, by decide, shift64_2348, rfl⟩
def row64:OrdinaryBounds.Source 2314 2411:=
  ⟨src64,⟨Research6969.TransitionBanks.rank259 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover64⟩⟩
private def src65:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,45081⟩,653560508579840,6296101689637⟩,195,3,1,385979,161⟩
private theorem shift65_2314 : (PhysicalWindow.Triangular src65) 2314 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift65_2337 : (PhysicalWindow.Triangular src65) 2337 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift65_2404 : (PhysicalWindow.Triangular src65) 2404 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover65 : PhysicalWindow.Cover (PhysicalWindow.Triangular src65) 2411 2314 [2336, 2403, 2411] := by
  exact ⟨by decide, by decide, shift65_2314, by decide, by decide, shift65_2337, by decide, by decide, shift65_2404, rfl⟩
def row65:OrdinaryBounds.Source 2314 2411:=
  ⟨src65,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover65⟩⟩
def row66:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1152,⟨Research6969.PackedRanks.TerminalRanks24To27.rank24 50764, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1152⟩⟩
private def src67:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,64247⟩,804053213511680,8288484232853⟩,250,3,1,385979,257⟩
private theorem shift67_2314 : (PhysicalWindow.Triangular src67) 2314 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift67_2328 : (PhysicalWindow.Triangular src67) 2328 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift67_2368 : (PhysicalWindow.Triangular src67) 2368 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover67 : PhysicalWindow.Cover (PhysicalWindow.Triangular src67) 2411 2314 [2327, 2367, 2411] := by
  exact ⟨by decide, by decide, shift67_2314, by decide, by decide, shift67_2328, by decide, by decide, shift67_2368, rfl⟩
def row67:OrdinaryBounds.Source 2314 2411:=
  ⟨src67,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover67⟩⟩
private def src68:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,3,1,385979,513⟩
private theorem shift68_2314 : (PhysicalWindow.Triangular src68) 2314 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift68_2325 : (PhysicalWindow.Triangular src68) 2325 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift68_2357 : (PhysicalWindow.Triangular src68) 2357 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover68 : PhysicalWindow.Cover (PhysicalWindow.Triangular src68) 2411 2314 [2324, 2356, 2411] := by
  exact ⟨by decide, by decide, shift68_2314, by decide, by decide, shift68_2325, by decide, by decide, shift68_2357, rfl⟩
def row68:OrdinaryBounds.Source 2314 2411:=
  ⟨src68,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover68⟩⟩
def row69:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1156,⟨Research6969.PackedRanks.TerminalRanks20To23.rank23 79852, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1156⟩⟩
private def src70:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,127905⟩,804053213511680,8269353083383⟩,325,3,1,385979,1025⟩
private theorem shift70_2314 : (PhysicalWindow.Triangular src70) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift70_2320 : (PhysicalWindow.Triangular src70) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift70_2337 : (PhysicalWindow.Triangular src70) 2337 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift70_2386 : (PhysicalWindow.Triangular src70) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover70 : PhysicalWindow.Cover (PhysicalWindow.Triangular src70) 2411 2314 [2319, 2336, 2385, 2411] := by
  exact ⟨by decide, by decide, shift70_2314, by decide, by decide, shift70_2320, by decide, by decide, shift70_2337, by decide, by decide, shift70_2386, rfl⟩
def row70:OrdinaryBounds.Source 2314 2411:=
  ⟨src70,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 127905, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover70⟩⟩
def row71:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1158,⟨Research6969.PackedRanks.TerminalRanks8To11.rank8 70068, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1158⟩⟩
def row72:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1161,⟨Research6969.PackedRanks.TerminalRanks56To59.rank56 157727, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1161⟩⟩
def row73:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1162,⟨Research6969.PackedRanks.TerminalRanks12To15.rank15 175105, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1162⟩⟩
private def src74:PhysicalWindow.Request := ⟨⟨⟨2000,2782,596,194349⟩,238428431581184,1632591172707⟩,250,3,1,385979,16385⟩
private theorem shift74_2314 : (PhysicalWindow.Triangular src74) 2314 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift74_2321 : (PhysicalWindow.Triangular src74) 2321 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift74_2341 : (PhysicalWindow.Triangular src74) 2341 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift74_2399 : (PhysicalWindow.Triangular src74) 2399 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover74 : PhysicalWindow.Cover (PhysicalWindow.Triangular src74) 2411 2314 [2320, 2340, 2398, 2411] := by
  exact ⟨by decide, by decide, shift74_2314, by decide, by decide, shift74_2321, by decide, by decide, shift74_2341, by decide, by decide, shift74_2399, rfl⟩
def row74:OrdinaryBounds.Source 2314 2411:=
  ⟨src74,⟨Research6969.PackedRanks.TerminalRanks12To15.rank14 194349, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover74⟩⟩
def row75:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1163,⟨Research6969.PackedRanks.TerminalRanks0To3.rank3 119707, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1163⟩⟩
private def src76:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,130242⟩,665461916958720,6440035562832⟩,45,4,1,514639,1⟩
private theorem shift76_2314 : (PhysicalWindow.Triangular src76) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift76_2319 : (PhysicalWindow.Triangular src76) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift76_2333 : (PhysicalWindow.Triangular src76) 2333 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift76_2372 : (PhysicalWindow.Triangular src76) 2372 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover76 : PhysicalWindow.Cover (PhysicalWindow.Triangular src76) 2411 2314 [2318, 2332, 2371, 2411] := by
  exact ⟨by decide, by decide, shift76_2314, by decide, by decide, shift76_2319, by decide, by decide, shift76_2333, by decide, by decide, shift76_2372, rfl⟩
def row76:OrdinaryBounds.Source 2314 2411:=
  ⟨src76,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 130242, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover76⟩⟩
private def src77:PhysicalWindow.Request := ⟨⟨⟨2300,3209,702,91474⟩,369170633195520,2936492475204⟩,32,4,1,514639,3⟩
private theorem shift77_2314 : (PhysicalWindow.Triangular src77) 2314 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift77_2324 : (PhysicalWindow.Triangular src77) 2324 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift77_2352 : (PhysicalWindow.Triangular src77) 2352 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover77 : PhysicalWindow.Cover (PhysicalWindow.Triangular src77) 2411 2314 [2323, 2351, 2411] := by
  exact ⟨by decide, by decide, shift77_2314, by decide, by decide, shift77_2324, by decide, by decide, shift77_2352, rfl⟩
def row77:OrdinaryBounds.Source 2314 2411:=
  ⟨src77,⟨Research6969.PackedRanks.TerminalRanks36To39.rank36 91474, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover77⟩⟩
private def src78:PhysicalWindow.Request := ⟨⟨⟨2300,3209,702,81311⟩,369170633195520,2936492475204⟩,32,4,1,514639,6⟩
private theorem shift78_2314 : (PhysicalWindow.Triangular src78) 2314 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift78_2322 : (PhysicalWindow.Triangular src78) 2322 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift78_2345 : (PhysicalWindow.Triangular src78) 2345 2408 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift78_2409 : (PhysicalWindow.Triangular src78) 2409 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover78 : PhysicalWindow.Cover (PhysicalWindow.Triangular src78) 2411 2314 [2321, 2344, 2408, 2411] := by
  exact ⟨by decide, by decide, shift78_2314, by decide, by decide, shift78_2322, by decide, by decide, shift78_2345, by decide, by decide, shift78_2409, rfl⟩
def row78:OrdinaryBounds.Source 2314 2411:=
  ⟨src78,⟨Research6969.PackedRanks.TerminalRanks36To39.rank36 81311, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover78⟩⟩
private def src79:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,91474⟩,665461916958720,6440035562832⟩,45,4,1,514639,10⟩
private theorem shift79_2314 : (PhysicalWindow.Triangular src79) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift79_2317 : (PhysicalWindow.Triangular src79) 2317 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift79_2325 : (PhysicalWindow.Triangular src79) 2325 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift79_2348 : (PhysicalWindow.Triangular src79) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover79 : PhysicalWindow.Cover (PhysicalWindow.Triangular src79) 2411 2314 [2316, 2324, 2347, 2411] := by
  exact ⟨by decide, by decide, shift79_2314, by decide, by decide, shift79_2317, by decide, by decide, shift79_2325, by decide, by decide, shift79_2348, rfl⟩
def row79:OrdinaryBounds.Source 2314 2411:=
  ⟨src79,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 91474, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover79⟩⟩
end Research6969.OrdSource
end Z6969Source0910

-- Source: Research6969.OrdinaryBooks
section Z6969Source0911
set_option autoImplicit true
namespace Research6969.OrdinaryBooks
open JointLedger
abbrev near:Book:=⟨234329630343844473,6143,133994566145700,1590006772040⟩
abbrev middle:Book:=⟨231373953658241386,6105,131528572298280,1592972508796⟩
abbrev nearQuadratic19:Book:=⟨232190986149640566,4851,124136401111740,1817642895608⟩
abbrev nearCubic41:Book:=⟨231590448761160043,4150,120708380414700,1818807159480⟩
abbrev nearQuintic26:Book:=⟨230390820158410918,4321,121629787325460,1818493958952⟩
end Research6969.OrdinaryBooks
end Z6969Source0911

end Merged_Z6969Pack0653

-- merged module Z6969Pack0654
section Merged_Z6969Pack0654

-- Source: Research6969.OrdChecks000
section Z6969Source0912
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell0:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,32769,none,128659,[OrdSource.row14],.excluded⟩
theorem checked0:cell0.check OrdinaryBooks.near 351:=by decide +kernel
def cell1:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,16385,some 32768,128659,[OrdSource.row13],.excluded⟩
theorem checked1:cell1.check OrdinaryBooks.near 351:=by decide +kernel
def cell2:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,8193,some 16384,128659,[OrdSource.row12],.excluded⟩
theorem checked2:cell2.check OrdinaryBooks.near 351:=by decide +kernel
def cell3:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,4097,some 8192,128659,[OrdSource.row11],.excluded⟩
theorem checked3:cell3.check OrdinaryBooks.near 351:=by decide +kernel
def cell4:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,2049,some 4096,128659,[OrdSource.row10],.excluded⟩
theorem checked4:cell4.check OrdinaryBooks.near 351:=by decide +kernel
def cell5:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,1025,some 2048,128659,[OrdSource.row9],.excluded⟩
theorem checked5:cell5.check OrdinaryBooks.near 351:=by decide +kernel
def cell6:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,513,some 1024,128659,[OrdSource.row7,OrdSource.row8],.marked⟩
theorem checked6:cell6.check OrdinaryBooks.near 351:=by decide +kernel
def cell7:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,257,some 512,128659,[OrdSource.row6],.marked⟩
theorem checked7:cell7.check OrdinaryBooks.near 351:=by decide +kernel
def cell8:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,161,some 256,128659,[OrdSource.row5],.marked⟩
theorem checked8:cell8.check OrdinaryBooks.near 351:=by decide +kernel
def cell9:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,97,some 160,128659,[OrdSource.row4],.marked⟩
theorem checked9:cell9.check OrdinaryBooks.near 351:=by decide +kernel
def cell10:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,65,some 96,128659,[OrdSource.row3],.marked⟩
theorem checked10:cell10.check OrdinaryBooks.near 351:=by decide +kernel
def cell11:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,48,some 64,128659,[OrdSource.row2],.affine⟩
theorem checked11:cell11.check OrdinaryBooks.near 351:=by decide +kernel
def cell12:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,36,some 47,128659,[OrdSource.row0],.affine⟩
theorem checked12:cell12.check OrdinaryBooks.near 351:=by decide +kernel
def cell13:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,27,some 35,128659,[],.affine⟩
theorem checked13:cell13.check OrdinaryBooks.near 351:=by decide +kernel
def cell14:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,21,some 26,128659,[],.affine⟩
theorem checked14:cell14.check OrdinaryBooks.near 351:=by decide +kernel
def cell15:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,15,some 20,128659,[],.affine⟩
theorem checked15:cell15.check OrdinaryBooks.near 351:=by decide +kernel
def cell16:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,10,some 14,128659,[],.affine⟩
theorem checked16:cell16.check OrdinaryBooks.near 351:=by decide +kernel
def cell17:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,6,some 9,128659,[],.affine⟩
theorem checked17:cell17.check OrdinaryBooks.near 351:=by decide +kernel
def cell18:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,3,some 5,128659,[],.affine⟩
theorem checked18:cell18.check OrdinaryBooks.near 351:=by decide +kernel
def cell19:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,1,some 2,128659,[],.affine⟩
theorem checked19:cell19.check OrdinaryBooks.near 351:=by decide +kernel
def cell20:OrdinaryCell.Row 2314 2411:=⟨22,22,9,1,0,some 0,128659,[],.affine⟩
theorem checked20:cell20.check OrdinaryBooks.near 351:=by decide +kernel
def cell21:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,32769,none,257319,[OrdSource.row46],.excluded⟩
theorem checked21:cell21.check OrdinaryBooks.near 351:=by decide +kernel
def cell22:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,16385,some 32768,257319,[OrdSource.row45],.excluded⟩
theorem checked22:cell22.check OrdinaryBooks.near 351:=by decide +kernel
def cell23:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,8193,some 16384,257319,[OrdSource.row44],.excluded⟩
theorem checked23:cell23.check OrdinaryBooks.near 351:=by decide +kernel
def cell24:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,4097,some 8192,257319,[OrdSource.row43],.excluded⟩
theorem checked24:cell24.check OrdinaryBooks.near 351:=by decide +kernel
def cell25:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,2049,some 4096,257319,[OrdSource.row42],.excluded⟩
theorem checked25:cell25.check OrdinaryBooks.near 351:=by decide +kernel
def cell26:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,1025,some 2048,257319,[OrdSource.row40,OrdSource.row41],.marked⟩
theorem checked26:cell26.check OrdinaryBooks.near 351:=by decide +kernel
def cell27:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,513,some 1024,257319,[OrdSource.row39],.marked⟩
theorem checked27:cell27.check OrdinaryBooks.near 351:=by decide +kernel
def cell28:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,257,some 512,257319,[OrdSource.row37,OrdSource.row38],.marked⟩
theorem checked28:cell28.check OrdinaryBooks.near 351:=by decide +kernel
def cell29:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,161,some 256,257319,[OrdSource.row36],.marked⟩
theorem checked29:cell29.check OrdinaryBooks.near 351:=by decide +kernel
def cell30:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,97,some 160,257319,[OrdSource.row33],.marked⟩
theorem checked30:cell30.check OrdinaryBooks.near 351:=by decide +kernel
def cell31:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,65,some 96,257319,[OrdSource.row30],.marked⟩
theorem checked31:cell31.check OrdinaryBooks.near 351:=by decide +kernel
def cell32:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,48,some 64,257319,[OrdSource.row23],.marked⟩
theorem checked32:cell32.check OrdinaryBooks.near 351:=by decide +kernel
def cell33:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,36,some 47,257319,[OrdSource.row19],.marked⟩
theorem checked33:cell33.check OrdinaryBooks.near 351:=by decide +kernel
def cell34:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,27,some 35,257319,[OrdSource.row15],.marked⟩
theorem checked34:cell34.check OrdinaryBooks.near 351:=by decide +kernel
def cell35:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,21,some 26,257319,[],.surface⟩
theorem checked35:cell35.check OrdinaryBooks.near 351:=by decide +kernel
def cell36:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,15,some 20,257319,[],.surface⟩
theorem checked36:cell36.check OrdinaryBooks.near 351:=by decide +kernel
def cell37:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,10,some 14,257319,[],.surface⟩
theorem checked37:cell37.check OrdinaryBooks.near 351:=by decide +kernel
def cell38:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,6,some 9,257319,[],.surface⟩
theorem checked38:cell38.check OrdinaryBooks.near 351:=by decide +kernel
def cell39:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,3,some 5,257319,[],.surface⟩
theorem checked39:cell39.check OrdinaryBooks.near 351:=by decide +kernel
def cell40:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,1,some 2,257319,[],.surface⟩
theorem checked40:cell40.check OrdinaryBooks.near 351:=by decide +kernel
def cell41:OrdinaryCell.Row 2314 2411:=⟨22,22,9,2,0,some 0,257319,[],.ambient⟩
theorem checked41:cell41.check OrdinaryBooks.near 351:=by decide +kernel
def cell42:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,32769,none,385979,[OrdSource.row75],.excluded⟩
theorem checked42:cell42.check OrdinaryBooks.near 351:=by decide +kernel
def cell43:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,16385,some 32768,385979,[OrdSource.row74],.excluded⟩
theorem checked43:cell43.check OrdinaryBooks.near 351:=by decide +kernel
def cell44:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,8193,some 16384,385979,[OrdSource.row73],.excluded⟩
theorem checked44:cell44.check OrdinaryBooks.near 351:=by decide +kernel
def cell45:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,4097,some 8192,385979,[OrdSource.row72],.marked⟩
theorem checked45:cell45.check OrdinaryBooks.near 351:=by decide +kernel
def cell46:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,2049,some 4096,385979,[OrdSource.row71],.marked⟩
theorem checked46:cell46.check OrdinaryBooks.near 351:=by decide +kernel
def cell47:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,1025,some 2048,385979,[OrdSource.row69,OrdSource.row70],.marked⟩
theorem checked47:cell47.check OrdinaryBooks.near 351:=by decide +kernel
def cell48:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,513,some 1024,385979,[OrdSource.row68],.marked⟩
theorem checked48:cell48.check OrdinaryBooks.near 351:=by decide +kernel
def cell49:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,257,some 512,385979,[OrdSource.row67],.marked⟩
theorem checked49:cell49.check OrdinaryBooks.near 351:=by decide +kernel
def cell50:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,161,some 256,385979,[OrdSource.row65],.marked⟩
theorem checked50:cell50.check OrdinaryBooks.near 351:=by decide +kernel
def cell51:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,97,some 160,385979,[OrdSource.row64],.marked⟩
theorem checked51:cell51.check OrdinaryBooks.near 351:=by decide +kernel
def cell52:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,65,some 96,385979,[OrdSource.row62],.marked⟩
theorem checked52:cell52.check OrdinaryBooks.near 351:=by decide +kernel
def cell53:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,48,some 64,385979,[OrdSource.row60],.marked⟩
theorem checked53:cell53.check OrdinaryBooks.near 351:=by decide +kernel
def cell54:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,36,some 47,385979,[OrdSource.row58],.marked⟩
theorem checked54:cell54.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0912

-- Source: Research6969.PhysicalChecks019
section Z6969Source0913
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1270 : Request := ⟨⟨⟨2800,3906,854,50450⟩,665461916958720,6440035562832⟩,45,4,1,514639,21⟩
theorem cover1270 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1270) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1271 : Request := ⟨⟨⟨2600,3626,775,208621⟩,523640687820800,4699589564453⟩,63,4,1,514639,21⟩
theorem cover1271 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1271) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1272 : Request := ⟨⟨⟨2600,3627,819,39802⟩,546063062138880,4910333421859⟩,45,4,1,514639,25⟩
theorem cover1272 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1272) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1273 : Request := ⟨⟨⟨2600,3626,775,146522⟩,523640687820800,4699589564453⟩,63,4,1,514639,25⟩
theorem cover1273 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1273) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src1284 : Request := ⟨⟨⟨2600,3626,775,91474⟩,523640687820800,4699589564453⟩,63,4,1,514639,29⟩
theorem cover1284 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1284) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src1285 : Request := ⟨⟨⟨2800,3905,854,50282⟩,665461916958720,6434729640882⟩,63,4,1,514639,29⟩
theorem cover1285 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1285) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1297 : Request := ⟨⟨⟨1750,2440,534,115771⟩,162688810352640,982675143308⟩,45,4,1,514639,33⟩
theorem cover1297 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1297) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1298 : Request := ⟨⟨⟨2800,3905,882,34312⟩,681932636815360,6598128215989⟩,63,4,1,514639,33⟩
theorem cover1298 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1298) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1328 : Request := ⟨⟨⟨2800,3905,854,45124⟩,665461916958720,6434729640882⟩,85,4,1,514639,41⟩
theorem cover1328 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1328) 2411 2314 [2325, 2359, 2411] := triangleCover (by decide +kernel)
def src1329 : Request := ⟨⟨⟨2800,3905,882,36829⟩,681932636815360,6598128215989⟩,85,4,1,514639,41⟩
theorem cover1329 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1329) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1352 : Request := ⟨⟨⟨2600,3625,775,31694⟩,523640687820800,4695421657977⟩,85,4,1,514639,49⟩
theorem cover1352 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1352) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1353 : Request := ⟨⟨⟨2600,3625,793,27673⟩,532875289296896,4780245027563⟩,85,4,1,514639,49⟩
theorem cover1353 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1353) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1369 : Request := ⟨⟨⟨2600,3624,793,35655⟩,532875289296896,4776001446129⟩,115,4,1,514639,65⟩
theorem cover1369 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1369) 2411 2314 [2334, 2394, 2411] := triangleCover (by decide +kernel)
def src1370 : Request := ⟨⟨⟨2600,3624,819,29473⟩,546063062138880,4897259437389⟩,115,4,1,514639,65⟩
theorem cover1370 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1370) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1371 : Request := ⟨⟨⟨2000,2787,610,31694⟩,242679148707840,1672034111214⟩,115,4,1,514639,97⟩
theorem cover1371 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1371) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
def src1372 : Request := ⟨⟨⟨2600,3623,793,34388⟩,532875289296896,4771760428124⟩,150,4,1,514639,97⟩
theorem cover1372 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1372) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0913

-- Source: Research6969.PhysicalChecks020
section Z6969Source0914
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1373 : Request := ⟨⟨⟨1750,2438,534,28225⟩,162688810352640,980085107193⟩,115,4,1,514639,129⟩
theorem cover1373 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1373) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1374 : Request := ⟨⟨⟨3000,4180,894,43391⟩,804053213511680,8301255031708⟩,195,4,1,514639,129⟩
theorem cover1374 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1374) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1375 : Request := ⟨⟨⟨2300,3203,702,45124⟩,369170633195520,2918855628076⟩,195,4,1,514639,257⟩
theorem cover1375 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1375) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1376 : Request := ⟨⟨⟨3000,4178,894,55750⟩,804053213511680,8288484232853⟩,250,4,1,514639,257⟩
theorem cover1376 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1376) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1377 : Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,4,1,514639,513⟩
theorem cover1377 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1377) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
def src1378 : Request := ⟨⟨⟨2600,3620,775,59805⟩,523640687820800,4674619806217⟩,250,4,1,514639,513⟩
theorem cover1378 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1378) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1379 : Request := ⟨⟨⟨1450,2018,432,49853⟩,90926432911360,452250342305⟩,150,4,1,514639,1025⟩
theorem cover1379 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1379) 2411 2314 [2330, 2381, 2411] := triangleCover (by decide +kernel)
def src1380 : Request := ⟨⟨⟨3000,4175,894,111774⟩,804053213511680,8269353083383⟩,325,4,1,514639,1025⟩
theorem cover1380 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1380) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1381 : Request := ⟨⟨⟨2800,3896,854,107262⟩,665461916958720,6387110095257⟩,325,4,1,514639,2049⟩
theorem cover1381 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1381) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1382 : Request := ⟨⟨⟨2800,3896,854,112233⟩,665461916958720,6387110095257⟩,325,4,1,514639,2049⟩
theorem cover1382 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1382) 2411 2314 [2321, 2344, 2409, 2411] := triangleCover (by decide +kernel)
def src1383 : Request := ⟨⟨⟨1000,1391,305,54645⟩,30406634373120,104212783664⟩,115,4,1,514639,4097⟩
theorem cover1383 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1383) 2411 2314 [2324, 2357, 2411] := triangleCover (by decide +kernel)
def src1384 : Request := ⟨⟨⟨2800,3896,812,153490⟩,640331821875200,6140432144913⟩,325,4,1,514639,4097⟩
theorem cover1384 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1384) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1385 : Request := ⟨⟨⟨2000,2782,610,175105⟩,242679148707840,1662397981334⟩,250,4,1,514639,8193⟩
theorem cover1385 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1385) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1386 : Request := ⟨⟨⟨1200,1669,366,119707⟩,52501327642624,215795999824⟩,150,4,1,514639,32769⟩
theorem cover1386 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1386) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1436 : Request := ⟨⟨⟨2300,3208,702,62341⟩,369170633195520,2933547980091⟩,45,5,1,643299,1⟩
theorem cover1436 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1436) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1437 : Request := ⟨⟨⟨2300,3207,702,530820⟩,369170633195520,2930605494152⟩,85,5,1,643299,1⟩
theorem cover1437 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1437) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0914

-- Source: Research6969.TerminalRanks4To7
section Z6969Source0915
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks4To7
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment1670_378 : P1_7_1.groupedPoleMoment 1670 378 ≤ 221692026804 :=
  _root_.PoleAffine6970.certified 1670 378 221692026804 (by decide) (by decide +kernel)

theorem moment2018_432 : P1_7_1.groupedPoleMoment 2018 432 ≤ 452250342305 :=
  _root_.PoleAffine6970.certified 2018 432 452250342305 (by decide) (by decide +kernel)

theorem moment2020_442 : P1_7_1.groupedPoleMoment 2020 442 ≤ 461852681878 :=
  _root_.PoleAffine6970.certified 2020 442 461852681878 (by decide) (by decide +kernel)

theorem moment2020_457 : P1_7_1.groupedPoleMoment 2020 457 ≤ 473974537987 :=
  _root_.PoleAffine6970.certified 2020 457 473974537987 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks4To7

namespace Research6969.PackedRanks.TerminalRanks4To7
open Research6969.TerminalAuxBanks
theorem rank4 (u:ℕ) : P3_7_1.BankOK (bank4 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank4 u).shape (by change 2*378≤1200;decide) (by change 1200+378≤1670+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1200-2*378) 378=6*53798525730816:=by decide
  change 6*P1_7_1.nodeRows (bank4 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank4 u).shape=262144*P1_7_1_2.sixPerNode (1200-2*378) 378 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank4 u).shape=53798525730816; omega, moment1670_378,by change 1670<K1.p;decide⟩
theorem rank5 (u:ℕ) : P3_7_1.BankOK (bank5 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank5 u).shape (by change 2*432≤1450;decide) (by change 1450+432≤2018+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1450-2*432) 432=6*90926432911360:=by decide
  change 6*P1_7_1.nodeRows (bank5 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank5 u).shape=262144*P1_7_1_2.sixPerNode (1450-2*432) 432 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank5 u).shape=90926432911360; omega, moment2018_432,by change 2018<K1.p;decide⟩
theorem rank6 (u:ℕ) : P3_7_1.BankOK (bank6 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank6 u).shape (by change 2*442≤1450;decide) (by change 1450+442≤2020+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1450-2*442) 442=6*92522927882240:=by decide
  change 6*P1_7_1.nodeRows (bank6 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank6 u).shape=262144*P1_7_1_2.sixPerNode (1450-2*442) 442 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank6 u).shape=92522927882240; omega, moment2020_442,by change 2020<K1.p;decide⟩
theorem rank7 (u:ℕ) : P3_7_1.BankOK (bank7 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank7 u).shape (by change 2*457≤1450;decide) (by change 1450+457≤2020+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1450-2*457) 457=6*94890063298560:=by decide
  change 6*P1_7_1.nodeRows (bank7 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank7 u).shape=262144*P1_7_1_2.sixPerNode (1450-2*457) 457 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank7 u).shape=94890063298560; omega, moment2020_457,by change 2020<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks4To7
end Z6969Source0915

-- Source: Research6969.OrdSource05
section Z6969Source0916
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src80:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,72277⟩,665461916958720,6440035562832⟩,45,4,1,514639,15⟩
private theorem shift80_2314 : (PhysicalWindow.Triangular src80) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift80_2318 : (PhysicalWindow.Triangular src80) 2318 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift80_2329 : (PhysicalWindow.Triangular src80) 2329 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift80_2360 : (PhysicalWindow.Triangular src80) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover80 : PhysicalWindow.Cover (PhysicalWindow.Triangular src80) 2411 2314 [2317, 2328, 2359, 2411] := by
  exact ⟨by decide, by decide, shift80_2314, by decide, by decide, shift80_2318, by decide, by decide, shift80_2329, by decide, by decide, shift80_2360, rfl⟩
def row80:OrdinaryBounds.Source 2314 2411:=
  ⟨src80,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 72277, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover80⟩⟩
private def src81:PhysicalWindow.Request := ⟨⟨⟨2800,3906,854,50764⟩,665461916958720,6440035562832⟩,45,4,1,514639,21⟩
private theorem shift81_2314 : (PhysicalWindow.Triangular src81) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift81_2317 : (PhysicalWindow.Triangular src81) 2317 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift81_2326 : (PhysicalWindow.Triangular src81) 2326 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift81_2351 : (PhysicalWindow.Triangular src81) 2351 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover81 : PhysicalWindow.Cover (PhysicalWindow.Triangular src81) 2411 2314 [2316, 2325, 2350, 2411] := by
  exact ⟨by decide, by decide, shift81_2314, by decide, by decide, shift81_2317, by decide, by decide, shift81_2326, by decide, by decide, shift81_2351, rfl⟩
def row81:OrdinaryBounds.Source 2314 2411:=
  ⟨src81,⟨Research6969.PackedRanks.TerminalRanks68To71.rank69 50764, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover81⟩⟩
private def src82:PhysicalWindow.Request := ⟨⟨⟨2600,3627,793,35655⟩,532875289296896,4788739883894⟩,45,4,1,514639,27⟩
private theorem shift82_2314 : (PhysicalWindow.Triangular src82) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift82_2318 : (PhysicalWindow.Triangular src82) 2318 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift82_2330 : (PhysicalWindow.Triangular src82) 2330 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift82_2363 : (PhysicalWindow.Triangular src82) 2363 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover82 : PhysicalWindow.Cover (PhysicalWindow.Triangular src82) 2411 2314 [2317, 2329, 2362, 2411] := by
  exact ⟨by decide, by decide, shift82_2314, by decide, by decide, shift82_2318, by decide, by decide, shift82_2330, by decide, by decide, shift82_2363, rfl⟩
def row82:OrdinaryBounds.Source 2314 2411:=
  ⟨src82,⟨Research6969.PackedRanks.TerminalRanks48To51.rank51 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover82⟩⟩
private def src83:PhysicalWindow.Request := ⟨⟨⟨2600,3626,793,31694⟩,532875289296896,4784491173220⟩,63,4,1,514639,36⟩
private theorem shift83_2314 : (PhysicalWindow.Triangular src83) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift83_2317 : (PhysicalWindow.Triangular src83) 2317 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift83_2325 : (PhysicalWindow.Triangular src83) 2325 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift83_2348 : (PhysicalWindow.Triangular src83) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover83 : PhysicalWindow.Cover (PhysicalWindow.Triangular src83) 2411 2314 [2316, 2324, 2347, 2411] := by
  exact ⟨by decide, by decide, shift83_2314, by decide, by decide, shift83_2317, by decide, by decide, shift83_2325, by decide, by decide, shift83_2348, rfl⟩
def row83:OrdinaryBounds.Source 2314 2411:=
  ⟨src83,⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover83⟩⟩
private def src84:PhysicalWindow.Request := ⟨⟨⟨2600,3625,819,28173⟩,546063062138880,4901614794409⟩,85,4,1,514639,48⟩
private theorem shift84_2314 : (PhysicalWindow.Triangular src84) 2314 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift84_2326 : (PhysicalWindow.Triangular src84) 2326 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift84_2360 : (PhysicalWindow.Triangular src84) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover84 : PhysicalWindow.Cover (PhysicalWindow.Triangular src84) 2411 2314 [2325, 2359, 2411] := by
  exact ⟨by decide, by decide, shift84_2314, by decide, by decide, shift84_2326, by decide, by decide, shift84_2360, rfl⟩
def row84:OrdinaryBounds.Source 2314 2411:=
  ⟨src84,⟨Research6969.TransitionBanks.rank263 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover84⟩⟩
private def src85:PhysicalWindow.Request := ⟨⟨⟨2600,3624,819,31694⟩,546063062138880,4897259437389⟩,115,4,1,514639,65⟩
private theorem shift85_2314 : (PhysicalWindow.Triangular src85) 2314 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift85_2333 : (PhysicalWindow.Triangular src85) 2333 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift85_2387 : (PhysicalWindow.Triangular src85) 2387 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover85 : PhysicalWindow.Cover (PhysicalWindow.Triangular src85) 2411 2314 [2332, 2386, 2411] := by
  exact ⟨by decide, by decide, shift85_2314, by decide, by decide, shift85_2333, by decide, by decide, shift85_2387, rfl⟩
def row85:OrdinaryBounds.Source 2314 2411:=
  ⟨src85,⟨Research6969.PackedRanks.TerminalRanks44To47.rank44 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover85⟩⟩
def row86:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1371,⟨Research6969.PackedRanks.TerminalRanks16To19.rank17 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1371⟩⟩
private def src87:PhysicalWindow.Request := ⟨⟨⟨2600,3623,793,35655⟩,532875289296896,4771760428124⟩,150,4,1,514639,97⟩
private theorem shift87_2314 : (PhysicalWindow.Triangular src87) 2314 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift87_2323 : (PhysicalWindow.Triangular src87) 2323 2348 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift87_2349 : (PhysicalWindow.Triangular src87) 2349 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover87 : PhysicalWindow.Cover (PhysicalWindow.Triangular src87) 2411 2314 [2322, 2348, 2411] := by
  exact ⟨by decide, by decide, shift87_2314, by decide, by decide, shift87_2323, by decide, by decide, shift87_2349, rfl⟩
def row87:OrdinaryBounds.Source 2314 2411:=
  ⟨src87,⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover87⟩⟩
private def src88:PhysicalWindow.Request := ⟨⟨⟨2600,3621,819,45081⟩,546063062138880,4884209183309⟩,195,4,1,514639,161⟩
private theorem shift88_2314 : (PhysicalWindow.Triangular src88) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift88_2319 : (PhysicalWindow.Triangular src88) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift88_2333 : (PhysicalWindow.Triangular src88) 2333 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift88_2372 : (PhysicalWindow.Triangular src88) 2372 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover88 : PhysicalWindow.Cover (PhysicalWindow.Triangular src88) 2411 2314 [2318, 2332, 2371, 2411] := by
  exact ⟨by decide, by decide, shift88_2314, by decide, by decide, shift88_2319, by decide, by decide, shift88_2333, by decide, by decide, shift88_2372, rfl⟩
def row88:OrdinaryBounds.Source 2314 2411:=
  ⟨src88,⟨Research6969.PackedRanks.OrdRanks4To5.rank4 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover88⟩⟩
private def src89:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,40072⟩,653560508579840,6296101689637⟩,195,4,1,514639,161⟩
private theorem shift89_2314 : (PhysicalWindow.Triangular src89) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift89_2320 : (PhysicalWindow.Triangular src89) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift89_2337 : (PhysicalWindow.Triangular src89) 2337 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift89_2386 : (PhysicalWindow.Triangular src89) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover89 : PhysicalWindow.Cover (PhysicalWindow.Triangular src89) 2411 2314 [2319, 2336, 2385, 2411] := by
  exact ⟨by decide, by decide, shift89_2314, by decide, by decide, shift89_2320, by decide, by decide, shift89_2337, by decide, by decide, shift89_2386, rfl⟩
def row89:OrdinaryBounds.Source 2314 2411:=
  ⟨src89,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 40072, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover89⟩⟩
def row90:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1375,⟨Research6969.PackedRanks.TerminalRanks24To27.rank24 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1375⟩⟩
private def src91:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,4,1,514639,257⟩
private theorem shift91_2314 : (PhysicalWindow.Triangular src91) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift91_2320 : (PhysicalWindow.Triangular src91) 2320 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift91_2338 : (PhysicalWindow.Triangular src91) 2338 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift91_2389 : (PhysicalWindow.Triangular src91) 2389 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover91 : PhysicalWindow.Cover (PhysicalWindow.Triangular src91) 2411 2314 [2319, 2337, 2388, 2411] := by
  exact ⟨by decide, by decide, shift91_2314, by decide, by decide, shift91_2320, by decide, by decide, shift91_2338, by decide, by decide, shift91_2389, rfl⟩
def row91:OrdinaryBounds.Source 2314 2411:=
  ⟨src91,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover91⟩⟩
def row92:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1377,⟨Research6969.PackedRanks.TerminalRanks16To19.rank16 50419, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1377⟩⟩
private def src93:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,4,1,514639,513⟩
private theorem shift93_2314 : (PhysicalWindow.Triangular src93) 2314 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift93_2327 : (PhysicalWindow.Triangular src93) 2327 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift93_2365 : (PhysicalWindow.Triangular src93) 2365 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover93 : PhysicalWindow.Cover (PhysicalWindow.Triangular src93) 2411 2314 [2326, 2364, 2411] := by
  exact ⟨by decide, by decide, shift93_2314, by decide, by decide, shift93_2327, by decide, by decide, shift93_2365, rfl⟩
def row93:OrdinaryBounds.Source 2314 2411:=
  ⟨src93,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover93⟩⟩
def row94:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1379,⟨Research6969.PackedRanks.TerminalRanks4To7.rank5 49853, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1379⟩⟩
private def src95:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,113694⟩,804053213511680,8269353083383⟩,325,4,1,514639,1025⟩
private theorem shift95_2314 : (PhysicalWindow.Triangular src95) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift95_2317 : (PhysicalWindow.Triangular src95) 2317 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift95_2326 : (PhysicalWindow.Triangular src95) 2326 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift95_2352 : (PhysicalWindow.Triangular src95) 2352 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover95 : PhysicalWindow.Cover (PhysicalWindow.Triangular src95) 2411 2314 [2316, 2325, 2351, 2411] := by
  exact ⟨by decide, by decide, shift95_2314, by decide, by decide, shift95_2317, by decide, by decide, shift95_2326, by decide, by decide, shift95_2352, rfl⟩
def row95:OrdinaryBounds.Source 2314 2411:=
  ⟨src95,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 113694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover95⟩⟩
end Research6969.OrdSource
end Z6969Source0916

-- Source: Research6969.OrdSource06
section Z6969Source0917
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def row96:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1382,⟨Research6969.PackedRanks.TerminalRanks56To59.rank57 112233, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1382⟩⟩
def row97:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1383,⟨Research6969.PackedRanks.TerminalRanks0To3.rank2 54645, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1383⟩⟩
def row98:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1385,⟨Research6969.PackedRanks.TerminalRanks12To15.rank15 175105, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1385⟩⟩
private def src99:PhysicalWindow.Request := ⟨⟨⟨1200,1669,378,121332⟩,53798525730816,221264762670⟩,150,4,1,514639,16385⟩
private theorem shift99_2314 : (PhysicalWindow.Triangular src99) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift99_2319 : (PhysicalWindow.Triangular src99) 2319 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift99_2334 : (PhysicalWindow.Triangular src99) 2334 2376 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift99_2377 : (PhysicalWindow.Triangular src99) 2377 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover99 : PhysicalWindow.Cover (PhysicalWindow.Triangular src99) 2411 2314 [2318, 2333, 2376, 2411] := by
  exact ⟨by decide, by decide, shift99_2314, by decide, by decide, shift99_2319, by decide, by decide, shift99_2334, by decide, by decide, shift99_2377, rfl⟩
def row99:OrdinaryBounds.Source 2314 2411:=
  ⟨src99,⟨Research6969.PackedRanks.OrdRanks0To3.rank1 121332, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover99⟩⟩
def row100:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1386,⟨Research6969.PackedRanks.TerminalRanks0To3.rank3 119707, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1386⟩⟩
private def src101:PhysicalWindow.Request := ⟨⟨⟨2300,3208,702,64247⟩,369170633195520,2933547980091⟩,45,5,1,643299,1⟩
private theorem shift101_2314 : (PhysicalWindow.Triangular src101) 2314 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift101_2326 : (PhysicalWindow.Triangular src101) 2326 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift101_2360 : (PhysicalWindow.Triangular src101) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover101 : PhysicalWindow.Cover (PhysicalWindow.Triangular src101) 2411 2314 [2325, 2359, 2411] := by
  exact ⟨by decide, by decide, shift101_2314, by decide, by decide, shift101_2326, by decide, by decide, shift101_2360, rfl⟩
def row101:OrdinaryBounds.Source 2314 2411:=
  ⟨src101,⟨Research6969.PackedRanks.TerminalRanks32To35.rank33 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover101⟩⟩
private def src102:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,81311⟩,665461916958720,6434729640882⟩,63,5,1,643299,3⟩
private theorem shift102_2314 : (PhysicalWindow.Triangular src102) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift102_2318 : (PhysicalWindow.Triangular src102) 2318 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift102_2329 : (PhysicalWindow.Triangular src102) 2329 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift102_2360 : (PhysicalWindow.Triangular src102) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover102 : PhysicalWindow.Cover (PhysicalWindow.Triangular src102) 2411 2314 [2317, 2328, 2359, 2411] := by
  exact ⟨by decide, by decide, shift102_2314, by decide, by decide, shift102_2318, by decide, by decide, shift102_2329, by decide, by decide, shift102_2360, rfl⟩
def row102:OrdinaryBounds.Source 2314 2411:=
  ⟨src102,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 81311, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover102⟩⟩
private def src103:PhysicalWindow.Request := ⟨⟨⟨2300,3208,702,57109⟩,369170633195520,2933547980091⟩,45,5,1,643299,6⟩
private theorem shift103_2314 : (PhysicalWindow.Triangular src103) 2314 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift103_2332 : (PhysicalWindow.Triangular src103) 2332 2382 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift103_2383 : (PhysicalWindow.Triangular src103) 2383 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover103 : PhysicalWindow.Cover (PhysicalWindow.Triangular src103) 2411 2314 [2331, 2382, 2411] := by
  exact ⟨by decide, by decide, shift103_2314, by decide, by decide, shift103_2332, by decide, by decide, shift103_2383, rfl⟩
def row103:OrdinaryBounds.Source 2314 2411:=
  ⟨src103,⟨Research6969.PackedRanks.TerminalRanks32To35.rank33 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover103⟩⟩
private def src104:PhysicalWindow.Request := ⟨⟨⟨2600,3626,793,72277⟩,532875289296896,4784491173220⟩,63,5,1,643299,10⟩
private theorem shift104_2314 : (PhysicalWindow.Triangular src104) 2314 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift104_2328 : (PhysicalWindow.Triangular src104) 2328 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift104_2368 : (PhysicalWindow.Triangular src104) 2368 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover104 : PhysicalWindow.Cover (PhysicalWindow.Triangular src104) 2411 2314 [2327, 2367, 2411] := by
  exact ⟨by decide, by decide, shift104_2314, by decide, by decide, shift104_2328, by decide, by decide, shift104_2368, rfl⟩
def row104:OrdinaryBounds.Source 2314 2411:=
  ⟨src104,⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 72277, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover104⟩⟩
private def src105:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,57109⟩,665461916958720,6434729640882⟩,63,5,1,643299,15⟩
private theorem shift105_2314 : (PhysicalWindow.Triangular src105) 2314 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift105_2323 : (PhysicalWindow.Triangular src105) 2323 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift105_2348 : (PhysicalWindow.Triangular src105) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover105 : PhysicalWindow.Cover (PhysicalWindow.Triangular src105) 2411 2314 [2322, 2347, 2411] := by
  exact ⟨by decide, by decide, shift105_2314, by decide, by decide, shift105_2323, by decide, by decide, shift105_2348, rfl⟩
def row105:OrdinaryBounds.Source 2314 2411:=
  ⟨src105,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover105⟩⟩
private def src106:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,45124⟩,665461916958720,6434729640882⟩,63,5,1,643299,21⟩
private theorem shift106_2314 : (PhysicalWindow.Triangular src106) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift106_2318 : (PhysicalWindow.Triangular src106) 2318 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift106_2329 : (PhysicalWindow.Triangular src106) 2329 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift106_2360 : (PhysicalWindow.Triangular src106) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover106 : PhysicalWindow.Cover (PhysicalWindow.Triangular src106) 2411 2314 [2317, 2328, 2359, 2411] := by
  exact ⟨by decide, by decide, shift106_2314, by decide, by decide, shift106_2318, by decide, by decide, shift106_2329, by decide, by decide, shift106_2360, rfl⟩
def row106:OrdinaryBounds.Source 2314 2411:=
  ⟨src106,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover106⟩⟩
private def src107:PhysicalWindow.Request := ⟨⟨⟨2600,3626,819,35655⟩,546063062138880,4905972788959⟩,63,5,1,643299,27⟩
private theorem shift107_2314 : (PhysicalWindow.Triangular src107) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift107_2320 : (PhysicalWindow.Triangular src107) 2320 2335 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift107_2336 : (PhysicalWindow.Triangular src107) 2336 2380 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift107_2381 : (PhysicalWindow.Triangular src107) 2381 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover107 : PhysicalWindow.Cover (PhysicalWindow.Triangular src107) 2411 2314 [2319, 2335, 2380, 2411] := by
  exact ⟨by decide, by decide, shift107_2314, by decide, by decide, shift107_2320, by decide, by decide, shift107_2336, by decide, by decide, shift107_2381, rfl⟩
def row107:OrdinaryBounds.Source 2314 2411:=
  ⟨src107,⟨Research6969.TransitionBanks.rank265 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover107⟩⟩
private def src108:PhysicalWindow.Request := ⟨⟨⟨2800,3905,882,35655⟩,681932636815360,6598128215989⟩,85,5,1,643299,36⟩
private theorem shift108_2314 : (PhysicalWindow.Triangular src108) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift108_2317 : (PhysicalWindow.Triangular src108) 2317 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift108_2325 : (PhysicalWindow.Triangular src108) 2325 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift108_2348 : (PhysicalWindow.Triangular src108) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover108 : PhysicalWindow.Cover (PhysicalWindow.Triangular src108) 2411 2314 [2316, 2324, 2347, 2411] := by
  exact ⟨by decide, by decide, shift108_2314, by decide, by decide, shift108_2317, by decide, by decide, shift108_2325, by decide, by decide, shift108_2348, rfl⟩
def row108:OrdinaryBounds.Source 2314 2411:=
  ⟨src108,⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover108⟩⟩
private def src109:PhysicalWindow.Request := ⟨⟨⟨2300,3207,724,28173⟩,377903408742400,3001726552718⟩,85,5,1,643299,48⟩
private theorem shift109_2314 : (PhysicalWindow.Triangular src109) 2314 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift109_2322 : (PhysicalWindow.Triangular src109) 2322 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift109_2345 : (PhysicalWindow.Triangular src109) 2345 2409 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift109_2410 : (PhysicalWindow.Triangular src109) 2410 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover109 : PhysicalWindow.Cover (PhysicalWindow.Triangular src109) 2411 2314 [2321, 2344, 2409, 2411] := by
  exact ⟨by decide, by decide, shift109_2314, by decide, by decide, shift109_2322, by decide, by decide, shift109_2345, by decide, by decide, shift109_2410, rfl⟩
def row109:OrdinaryBounds.Source 2314 2411:=
  ⟨src109,⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover109⟩⟩
private def src110:PhysicalWindow.Request := ⟨⟨⟨2600,3624,819,28173⟩,546063062138880,4897259437389⟩,115,5,1,643299,65⟩
private theorem shift110_2314 : (PhysicalWindow.Triangular src110) 2314 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift110_2328 : (PhysicalWindow.Triangular src110) 2328 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift110_2367 : (PhysicalWindow.Triangular src110) 2367 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover110 : PhysicalWindow.Cover (PhysicalWindow.Triangular src110) 2411 2314 [2327, 2366, 2411] := by
  exact ⟨by decide, by decide, shift110_2314, by decide, by decide, shift110_2328, by decide, by decide, shift110_2367, rfl⟩
def row110:OrdinaryBounds.Source 2314 2411:=
  ⟨src110,⟨Research6969.PackedRanks.TerminalRanks44To47.rank44 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover110⟩⟩
private def src111:PhysicalWindow.Request := ⟨⟨⟨2600,3623,793,35655⟩,532875289296896,4771760428124⟩,150,5,1,643299,97⟩
private theorem shift111_2314 : (PhysicalWindow.Triangular src111) 2314 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift111_2342 : (PhysicalWindow.Triangular src111) 2342 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover111 : PhysicalWindow.Cover (PhysicalWindow.Triangular src111) 2411 2314 [2341, 2411] := by
  exact ⟨by decide, by decide, shift111_2314, by decide, by decide, shift111_2342, rfl⟩
def row111:OrdinaryBounds.Source 2314 2411:=
  ⟨src111,⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover111⟩⟩
end Research6969.OrdSource
end Z6969Source0917

-- Source: Research6969.PhysicalChecks022
section Z6969Source0918
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1508 : Request := ⟨⟨⟨2800,3905,854,43089⟩,665461916958720,6434729640882⟩,85,5,1,643299,33⟩
theorem cover1508 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1508) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1509 : Request := ⟨⟨⟨3000,4183,894,422931⟩,804053213511680,8320436296703⟩,115,5,1,643299,33⟩
theorem cover1509 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1509) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1517 : Request := ⟨⟨⟨2600,3625,819,30949⟩,546063062138880,4901614794409⟩,85,5,1,643299,41⟩
theorem cover1517 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1517) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1518 : Request := ⟨⟨⟨3000,4183,894,115771⟩,804053213511680,8320436296703⟩,115,5,1,643299,41⟩
theorem cover1518 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1518) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src1522 : Request := ⟨⟨⟨2300,3207,702,28031⟩,369170633195520,2930605494152⟩,85,5,1,643299,49⟩
theorem cover1522 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1522) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1523 : Request := ⟨⟨⟨2800,3903,854,50764⟩,665461916958720,6424126719762⟩,115,5,1,643299,49⟩
theorem cover1523 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1523) 2411 2314 [2321, 2343, 2405, 2411] := triangleCover (by decide +kernel)
def src1524 : Request := ⟨⟨⟨2600,3624,775,35655⟩,523640687820800,4691256264577⟩,115,5,1,643299,65⟩
theorem cover1524 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1524) 2411 2314 [2337, 2406, 2411] := triangleCover (by decide +kernel)
def src1525 : Request := ⟨⟨⟨2600,3624,819,27318⟩,546063062138880,4897259437389⟩,115,5,1,643299,65⟩
theorem cover1525 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1525) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1526 : Request := ⟨⟨⟨1450,2020,457,25043⟩,94890063298560,473974537987⟩,85,5,1,643299,97⟩
theorem cover1526 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1526) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src1527 : Request := ⟨⟨⟨2600,3623,819,30471⟩,546063062138880,4892906717079⟩,150,5,1,643299,97⟩
theorem cover1527 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1527) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1528 : Request := ⟨⟨⟨2800,3901,882,43654⟩,681932636815360,6576375970149⟩,195,5,1,643299,129⟩
theorem cover1528 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1528) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1529 : Request := ⟨⟨⟨2800,3901,882,45210⟩,681932636815360,6576375970149⟩,195,5,1,643299,129⟩
theorem cover1529 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1529) 2411 2314 [2320, 2340, 2396, 2411] := triangleCover (by decide +kernel)
def src1530 : Request := ⟨⟨⟨1750,2437,551,40111⟩,166595992223744,1002904994165⟩,150,5,1,643299,257⟩
theorem cover1530 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1530) 2411 2314 [2318, 2333, 2375, 2411] := triangleCover (by decide +kernel)
def src1531 : Request := ⟨⟨⟨3000,4178,894,54275⟩,804053213511680,8288484232853⟩,250,5,1,643299,257⟩
theorem cover1531 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1531) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1532 : Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,5,1,643299,513⟩
theorem cover1532 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1532) 2411 2314 [2326, 2364, 2411] := triangleCover (by decide +kernel)
def src1533 : Request := ⟨⟨⟨2600,3620,775,59148⟩,523640687820800,4674619806217⟩,250,5,1,643299,513⟩
theorem cover1533 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1533) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0918

-- Source: Research6969.PhysicalChecks023
section Z6969Source0919
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1534 : Request := ⟨⟨⟨2300,3201,702,79852⟩,369170633195520,2912992731804⟩,250,5,1,643299,1025⟩
theorem cover1534 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1534) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src1535 : Request := ⟨⟨⟨3000,4175,894,109644⟩,804053213511680,8269353083383⟩,325,5,1,643299,1025⟩
theorem cover1535 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1535) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1536 : Request := ⟨⟨⟨2800,3896,882,134834⟩,681932636815360,6549254417644⟩,325,5,1,643299,1537⟩
theorem cover1536 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1536) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src1537 : Request := ⟨⟨⟨3000,4175,870,114085⟩,787488727367680,8095188217725⟩,325,5,1,643299,1537⟩
theorem cover1537 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1537) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1538 : Request := ⟨⟨⟨2800,3896,854,106975⟩,665461916958720,6387110095257⟩,325,5,1,643299,2049⟩
theorem cover1538 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1538) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1539 : Request := ⟨⟨⟨2800,3896,854,112233⟩,665461916958720,6387110095257⟩,325,5,1,643299,2049⟩
theorem cover1539 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1539) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src1540 : Request := ⟨⟨⟨2800,3896,812,153182⟩,640331821875200,6140432144913⟩,325,5,1,643299,4097⟩
theorem cover1540 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1540) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1541 : Request := ⟨⟨⟨2800,3896,812,157727⟩,640331821875200,6140432144913⟩,325,5,1,643299,4097⟩
theorem cover1541 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1541) 2411 2314 [2319, 2336, 2386, 2411] := triangleCover (by decide +kernel)
def src1542 : Request := ⟨⟨⟨2000,2782,610,175105⟩,242679148707840,1662397981334⟩,250,5,1,643299,8193⟩
theorem cover1542 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1542) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1543 : Request := ⟨⟨⟨1200,1669,366,119707⟩,52501327642624,215795999824⟩,150,5,1,643299,32769⟩
theorem cover1543 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1543) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1566 : Request := ⟨⟨⟨2800,3905,854,71586⟩,665461916958720,6434729640882⟩,85,6,1,771959,1⟩
theorem cover1566 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1566) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1567 : Request := ⟨⟨⟨2600,3624,775,264035⟩,523640687820800,4691256264577⟩,115,6,1,771959,1⟩
theorem cover1567 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1567) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src1578 : Request := ⟨⟨⟨2600,3626,819,50099⟩,546063062138880,4905972788959⟩,63,6,1,771959,2⟩
theorem cover1578 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1578) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src1580 : Request := ⟨⟨⟨2600,3624,775,264035⟩,523640687820800,4691256264577⟩,115,6,1,771959,2⟩
theorem cover1580 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1580) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1591 : Request := ⟨⟨⟨2300,3207,702,50171⟩,369170633195520,2930605494152⟩,63,6,1,771959,4⟩
theorem cover1591 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1591) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1594 : Request := ⟨⟨⟨2600,3624,775,264035⟩,523640687820800,4691256264577⟩,115,6,1,771959,4⟩
theorem cover1594 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1594) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0919

-- Source: Research6969.OrdSource07
section Z6969Source0920
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src112:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,40072⟩,653560508579840,6296101689637⟩,195,5,1,643299,161⟩
private theorem shift112_2314 : (PhysicalWindow.Triangular src112) 2314 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift112_2328 : (PhysicalWindow.Triangular src112) 2328 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift112_2368 : (PhysicalWindow.Triangular src112) 2368 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover112 : PhysicalWindow.Cover (PhysicalWindow.Triangular src112) 2411 2314 [2327, 2367, 2411] := by
  exact ⟨by decide, by decide, shift112_2314, by decide, by decide, shift112_2328, by decide, by decide, shift112_2368, rfl⟩
def row112:OrdinaryBounds.Source 2314 2411:=
  ⟨src112,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 40072, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover112⟩⟩
private def src113:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,5,1,643299,257⟩
private theorem shift113_2314 : (PhysicalWindow.Triangular src113) 2314 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift113_2326 : (PhysicalWindow.Triangular src113) 2326 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift113_2361 : (PhysicalWindow.Triangular src113) 2361 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover113 : PhysicalWindow.Cover (PhysicalWindow.Triangular src113) 2411 2314 [2325, 2360, 2411] := by
  exact ⟨by decide, by decide, shift113_2314, by decide, by decide, shift113_2326, by decide, by decide, shift113_2361, rfl⟩
def row113:OrdinaryBounds.Source 2314 2411:=
  ⟨src113,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover113⟩⟩
def row114:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1532,⟨Research6969.PackedRanks.TerminalRanks16To19.rank16 50419, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1532⟩⟩
private def src115:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,5,1,643299,513⟩
private theorem shift115_2314 : (PhysicalWindow.Triangular src115) 2314 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift115_2330 : (PhysicalWindow.Triangular src115) 2330 2375 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift115_2376 : (PhysicalWindow.Triangular src115) 2376 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover115 : PhysicalWindow.Cover (PhysicalWindow.Triangular src115) 2411 2314 [2329, 2375, 2411] := by
  exact ⟨by decide, by decide, shift115_2314, by decide, by decide, shift115_2330, by decide, by decide, shift115_2376, rfl⟩
def row115:OrdinaryBounds.Source 2314 2411:=
  ⟨src115,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover115⟩⟩
private def src116:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,113694⟩,804053213511680,8269353083383⟩,325,5,1,643299,1025⟩
private theorem shift116_2314 : (PhysicalWindow.Triangular src116) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift116_2319 : (PhysicalWindow.Triangular src116) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift116_2333 : (PhysicalWindow.Triangular src116) 2333 2372 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift116_2373 : (PhysicalWindow.Triangular src116) 2373 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover116 : PhysicalWindow.Cover (PhysicalWindow.Triangular src116) 2411 2314 [2318, 2332, 2372, 2411] := by
  exact ⟨by decide, by decide, shift116_2314, by decide, by decide, shift116_2319, by decide, by decide, shift116_2333, by decide, by decide, shift116_2373, rfl⟩
def row116:OrdinaryBounds.Source 2314 2411:=
  ⟨src116,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 113694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover116⟩⟩
def row117:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1541,⟨Research6969.PackedRanks.TerminalRanks56To59.rank56 157727, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1541⟩⟩
def row118:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1542,⟨Research6969.PackedRanks.TerminalRanks12To15.rank15 175105, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1542⟩⟩
private def src119:PhysicalWindow.Request := ⟨⟨⟨2000,2782,596,194349⟩,238428431581184,1632591172707⟩,250,5,1,643299,16385⟩
private theorem shift119_2314 : (PhysicalWindow.Triangular src119) 2314 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift119_2321 : (PhysicalWindow.Triangular src119) 2321 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift119_2341 : (PhysicalWindow.Triangular src119) 2341 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift119_2399 : (PhysicalWindow.Triangular src119) 2399 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover119 : PhysicalWindow.Cover (PhysicalWindow.Triangular src119) 2411 2314 [2320, 2340, 2398, 2411] := by
  exact ⟨by decide, by decide, shift119_2314, by decide, by decide, shift119_2321, by decide, by decide, shift119_2341, by decide, by decide, shift119_2399, rfl⟩
def row119:OrdinaryBounds.Source 2314 2411:=
  ⟨src119,⟨Research6969.PackedRanks.TerminalRanks12To15.rank14 194349, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover119⟩⟩
def row120:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src1543,⟨Research6969.PackedRanks.TerminalRanks0To3.rank3 119707, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover1543⟩⟩
private def src121:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,72277⟩,665461916958720,6434729640882⟩,85,6,1,771959,1⟩
private theorem shift121_2314 : (PhysicalWindow.Triangular src121) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift121_2319 : (PhysicalWindow.Triangular src121) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift121_2333 : (PhysicalWindow.Triangular src121) 2333 2372 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift121_2373 : (PhysicalWindow.Triangular src121) 2373 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover121 : PhysicalWindow.Cover (PhysicalWindow.Triangular src121) 2411 2314 [2318, 2332, 2372, 2411] := by
  exact ⟨by decide, by decide, shift121_2314, by decide, by decide, shift121_2319, by decide, by decide, shift121_2333, by decide, by decide, shift121_2373, rfl⟩
def row121:OrdinaryBounds.Source 2314 2411:=
  ⟨src121,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 72277, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover121⟩⟩
private def src122:PhysicalWindow.Request := ⟨⟨⟨2300,3207,724,50764⟩,377903408742400,3001726552718⟩,63,6,1,771959,3⟩
private theorem shift122_2314 : (PhysicalWindow.Triangular src122) 2314 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift122_2321 : (PhysicalWindow.Triangular src122) 2321 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift122_2341 : (PhysicalWindow.Triangular src122) 2341 2396 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift122_2397 : (PhysicalWindow.Triangular src122) 2397 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover122 : PhysicalWindow.Cover (PhysicalWindow.Triangular src122) 2411 2314 [2320, 2340, 2396, 2411] := by
  exact ⟨by decide, by decide, shift122_2314, by decide, by decide, shift122_2321, by decide, by decide, shift122_2341, by decide, by decide, shift122_2397, rfl⟩
def row122:OrdinaryBounds.Source 2314 2411:=
  ⟨src122,⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 50764, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover122⟩⟩
private def src123:PhysicalWindow.Request := ⟨⟨⟨2800,3905,882,64247⟩,681932636815360,6598128215989⟩,85,6,1,771959,6⟩
private theorem shift123_2314 : (PhysicalWindow.Triangular src123) 2314 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift123_2323 : (PhysicalWindow.Triangular src123) 2323 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift123_2348 : (PhysicalWindow.Triangular src123) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover123 : PhysicalWindow.Cover (PhysicalWindow.Triangular src123) 2411 2314 [2322, 2347, 2411] := by
  exact ⟨by decide, by decide, shift123_2314, by decide, by decide, shift123_2323, by decide, by decide, shift123_2348, rfl⟩
def row123:OrdinaryBounds.Source 2314 2411:=
  ⟨src123,⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover123⟩⟩
private def src124:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,45124⟩,369170633195520,2930605494152⟩,63,6,1,771959,10⟩
private theorem shift124_2314 : (PhysicalWindow.Triangular src124) 2314 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift124_2325 : (PhysicalWindow.Triangular src124) 2325 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift124_2356 : (PhysicalWindow.Triangular src124) 2356 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover124 : PhysicalWindow.Cover (PhysicalWindow.Triangular src124) 2411 2314 [2324, 2355, 2411] := by
  exact ⟨by decide, by decide, shift124_2314, by decide, by decide, shift124_2325, by decide, by decide, shift124_2356, rfl⟩
def row124:OrdinaryBounds.Source 2314 2411:=
  ⟨src124,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover124⟩⟩
private def src125:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,40111⟩,369170633195520,2930605494152⟩,63,6,1,771959,15⟩
private theorem shift125_2314 : (PhysicalWindow.Triangular src125) 2314 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift125_2324 : (PhysicalWindow.Triangular src125) 2324 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift125_2353 : (PhysicalWindow.Triangular src125) 2353 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover125 : PhysicalWindow.Cover (PhysicalWindow.Triangular src125) 2411 2314 [2323, 2352, 2411] := by
  exact ⟨by decide, by decide, shift125_2314, by decide, by decide, shift125_2324, by decide, by decide, shift125_2353, rfl⟩
def row125:OrdinaryBounds.Source 2314 2411:=
  ⟨src125,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 40111, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover125⟩⟩
private def src126:PhysicalWindow.Request := ⟨⟨⟨2800,3905,882,45124⟩,681932636815360,6598128215989⟩,85,6,1,771959,21⟩
private theorem shift126_2314 : (PhysicalWindow.Triangular src126) 2314 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift126_2326 : (PhysicalWindow.Triangular src126) 2326 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift126_2360 : (PhysicalWindow.Triangular src126) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover126 : PhysicalWindow.Cover (PhysicalWindow.Triangular src126) 2411 2314 [2325, 2359, 2411] := by
  exact ⟨by decide, by decide, shift126_2314, by decide, by decide, shift126_2326, by decide, by decide, shift126_2360, rfl⟩
def row126:OrdinaryBounds.Source 2314 2411:=
  ⟨src126,⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover126⟩⟩
private def src127:PhysicalWindow.Request := ⟨⟨⟨2600,3625,819,40111⟩,546063062138880,4901614794409⟩,85,6,1,771959,27⟩
private theorem shift127_2314 : (PhysicalWindow.Triangular src127) 2314 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift127_2326 : (PhysicalWindow.Triangular src127) 2326 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift127_2360 : (PhysicalWindow.Triangular src127) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover127 : PhysicalWindow.Cover (PhysicalWindow.Triangular src127) 2411 2314 [2325, 2359, 2411] := by
  exact ⟨by decide, by decide, shift127_2314, by decide, by decide, shift127_2326, by decide, by decide, shift127_2360, rfl⟩
def row127:OrdinaryBounds.Source 2314 2411:=
  ⟨src127,⟨Research6969.TransitionBanks.rank263 40111, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover127⟩⟩
end Research6969.OrdSource
end Z6969Source0920

-- Source: Research6969.OrdSource08
section Z6969Source0921
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src128:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,35655⟩,369170633195520,2930605494152⟩,85,6,1,771959,36⟩
private theorem shift128_2314 : (PhysicalWindow.Triangular src128) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift128_2318 : (PhysicalWindow.Triangular src128) 2318 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift128_2329 : (PhysicalWindow.Triangular src128) 2329 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift128_2360 : (PhysicalWindow.Triangular src128) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover128 : PhysicalWindow.Cover (PhysicalWindow.Triangular src128) 2411 2314 [2317, 2328, 2359, 2411] := by
  exact ⟨by decide, by decide, shift128_2314, by decide, by decide, shift128_2318, by decide, by decide, shift128_2329, by decide, by decide, shift128_2360, rfl⟩
def row128:OrdinaryBounds.Source 2314 2411:=
  ⟨src128,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover128⟩⟩
private def src129:PhysicalWindow.Request := ⟨⟨⟨2800,3903,882,35655⟩,681932636815360,6587245977411⟩,115,6,1,771959,48⟩
private theorem shift129_2314 : (PhysicalWindow.Triangular src129) 2314 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift129_2329 : (PhysicalWindow.Triangular src129) 2329 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift129_2371 : (PhysicalWindow.Triangular src129) 2371 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover129 : PhysicalWindow.Cover (PhysicalWindow.Triangular src129) 2411 2314 [2328, 2370, 2411] := by
  exact ⟨by decide, by decide, shift129_2314, by decide, by decide, shift129_2329, by decide, by decide, shift129_2371, rfl⟩
def row129:OrdinaryBounds.Source 2314 2411:=
  ⟨src129,⟨Research6969.PackedRanks.TerminalRanks64To67.rank65 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover129⟩⟩
private def src130:PhysicalWindow.Request := ⟨⟨⟨2300,3206,724,31694⟩,377903408742400,2998712046218⟩,115,6,1,771959,65⟩
private theorem shift130_2314 : (PhysicalWindow.Triangular src130) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift130_2320 : (PhysicalWindow.Triangular src130) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift130_2337 : (PhysicalWindow.Triangular src130) 2337 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift130_2385 : (PhysicalWindow.Triangular src130) 2385 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover130 : PhysicalWindow.Cover (PhysicalWindow.Triangular src130) 2411 2314 [2319, 2336, 2384, 2411] := by
  exact ⟨by decide, by decide, shift130_2314, by decide, by decide, shift130_2320, by decide, by decide, shift130_2337, by decide, by decide, shift130_2385, rfl⟩
def row130:OrdinaryBounds.Source 2314 2411:=
  ⟨src130,⟨Research6969.PackedRanks.TerminalRanks28To31.rank29 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover130⟩⟩
private def src131:PhysicalWindow.Request := ⟨⟨⟨2600,3623,793,31694⟩,532875289296896,4771760428124⟩,150,6,1,771959,97⟩
private theorem shift131_2314 : (PhysicalWindow.Triangular src131) 2314 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift131_2325 : (PhysicalWindow.Triangular src131) 2325 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift131_2356 : (PhysicalWindow.Triangular src131) 2356 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover131 : PhysicalWindow.Cover (PhysicalWindow.Triangular src131) 2411 2314 [2324, 2355, 2411] := by
  exact ⟨by decide, by decide, shift131_2314, by decide, by decide, shift131_2325, by decide, by decide, shift131_2356, rfl⟩
def row131:OrdinaryBounds.Source 2314 2411:=
  ⟨src131,⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover131⟩⟩
private def src132:PhysicalWindow.Request := ⟨⟨⟨2600,3621,793,45081⟩,532875289296896,4763286079225⟩,195,6,1,771959,161⟩
private theorem shift132_2314 : (PhysicalWindow.Triangular src132) 2314 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift132_2322 : (PhysicalWindow.Triangular src132) 2322 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift132_2345 : (PhysicalWindow.Triangular src132) 2345 2409 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift132_2410 : (PhysicalWindow.Triangular src132) 2410 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover132 : PhysicalWindow.Cover (PhysicalWindow.Triangular src132) 2411 2314 [2321, 2344, 2409, 2411] := by
  exact ⟨by decide, by decide, shift132_2314, by decide, by decide, shift132_2322, by decide, by decide, shift132_2345, by decide, by decide, shift132_2410, rfl⟩
def row132:OrdinaryBounds.Source 2314 2411:=
  ⟨src132,⟨Research6969.PackedRanks.OrdRanks0To3.rank3 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover132⟩⟩
private def src133:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,6,1,771959,257⟩
private theorem shift133_2314 : (PhysicalWindow.Triangular src133) 2314 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift133_2332 : (PhysicalWindow.Triangular src133) 2332 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift133_2384 : (PhysicalWindow.Triangular src133) 2384 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover133 : PhysicalWindow.Cover (PhysicalWindow.Triangular src133) 2411 2314 [2331, 2383, 2411] := by
  exact ⟨by decide, by decide, shift133_2314, by decide, by decide, shift133_2332, by decide, by decide, shift133_2384, rfl⟩
def row133:OrdinaryBounds.Source 2314 2411:=
  ⟨src133,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover133⟩⟩
private def src134:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,6,1,771959,513⟩
private theorem shift134_2314 : (PhysicalWindow.Triangular src134) 2314 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift134_2332 : (PhysicalWindow.Triangular src134) 2332 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift134_2384 : (PhysicalWindow.Triangular src134) 2384 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover134 : PhysicalWindow.Cover (PhysicalWindow.Triangular src134) 2411 2314 [2331, 2383, 2411] := by
  exact ⟨by decide, by decide, shift134_2314, by decide, by decide, shift134_2332, by decide, by decide, shift134_2384, rfl⟩
def row134:OrdinaryBounds.Source 2314 2411:=
  ⟨src134,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover134⟩⟩
private def src135:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,113694⟩,804053213511680,8269353083383⟩,325,6,1,771959,1025⟩
private theorem shift135_2314 : (PhysicalWindow.Triangular src135) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift135_2320 : (PhysicalWindow.Triangular src135) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift135_2337 : (PhysicalWindow.Triangular src135) 2337 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift135_2386 : (PhysicalWindow.Triangular src135) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover135 : PhysicalWindow.Cover (PhysicalWindow.Triangular src135) 2411 2314 [2319, 2336, 2385, 2411] := by
  exact ⟨by decide, by decide, shift135_2314, by decide, by decide, shift135_2320, by decide, by decide, shift135_2337, by decide, by decide, shift135_2386, rfl⟩
def row135:OrdinaryBounds.Source 2314 2411:=
  ⟨src135,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 113694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover135⟩⟩
private def src136:PhysicalWindow.Request := ⟨⟨⟨2800,3906,882,28173⟩,681932636815360,6603573924229⟩,32,1,1,128513,36⟩
private theorem shift136_2412 : (PhysicalWindow.Triangular src136) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover136 : PhysicalWindow.Cover (PhysicalWindow.Triangular src136) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift136_2412, rfl⟩
def row136:OrdinaryBounds.Source 2412 2557:=
  ⟨src136,⟨Research6969.PackedRanks.TerminalRanks68To71.rank70 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover136⟩⟩
private def src137:PhysicalWindow.Request := ⟨⟨⟨2600,3626,793,28173⟩,532875289296896,4784491173220⟩,63,1,1,128513,48⟩
private theorem shift137_2412 : (PhysicalWindow.Triangular src137) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover137 : PhysicalWindow.Cover (PhysicalWindow.Triangular src137) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift137_2412, rfl⟩
def row137:OrdinaryBounds.Source 2412 2557:=
  ⟨src137,⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover137⟩⟩
private def src138:PhysicalWindow.Request := ⟨⟨⟨2600,3626,819,25043⟩,546063062138880,4905972788959⟩,63,1,1,128513,48⟩
private theorem shift138_2412 : (PhysicalWindow.Triangular src138) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover138 : PhysicalWindow.Cover (PhysicalWindow.Triangular src138) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift138_2412, rfl⟩
def row138:OrdinaryBounds.Source 2412 2557:=
  ⟨src138,⟨Research6969.TransitionBanks.rank265 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover138⟩⟩
private def src139:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,25043⟩,369170633195520,2930605494152⟩,85,1,1,128513,65⟩
private theorem shift139_2412 : (PhysicalWindow.Triangular src139) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover139 : PhysicalWindow.Cover (PhysicalWindow.Triangular src139) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift139_2412, rfl⟩
def row139:OrdinaryBounds.Source 2412 2557:=
  ⟨src139,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover139⟩⟩
private def src140:PhysicalWindow.Request := ⟨⟨⟨2800,3902,854,35655⟩,665461916958720,6418829718882⟩,150,1,1,128513,97⟩
private theorem shift140_2412 : (PhysicalWindow.Triangular src140) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover140 : PhysicalWindow.Cover (PhysicalWindow.Triangular src140) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift140_2412, rfl⟩
def row140:OrdinaryBounds.Source 2412 2557:=
  ⟨src140,⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover140⟩⟩
private def src141:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,45081⟩,653560508579840,6296101689637⟩,195,1,1,128513,161⟩
private theorem shift141_2412 : (PhysicalWindow.Triangular src141) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover141 : PhysicalWindow.Cover (PhysicalWindow.Triangular src141) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift141_2412, rfl⟩
def row141:OrdinaryBounds.Source 2412 2557:=
  ⟨src141,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover141⟩⟩
private def src142:PhysicalWindow.Request := ⟨⟨⟨2300,3203,724,45124⟩,377903408742400,2989680899568⟩,195,1,1,128513,257⟩
private theorem shift142_2412 : (PhysicalWindow.Triangular src142) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover142 : PhysicalWindow.Cover (PhysicalWindow.Triangular src142) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift142_2412, rfl⟩
def row142:OrdinaryBounds.Source 2412 2557:=
  ⟨src142,⟨Research6969.PackedRanks.TerminalRanks24To27.rank25 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover142⟩⟩
private def src143:PhysicalWindow.Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,1,1,128513,513⟩
private theorem shift143_2412 : (PhysicalWindow.Triangular src143) 2412 2557 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover143 : PhysicalWindow.Cover (PhysicalWindow.Triangular src143) 2557 2412 [2557] := by
  exact ⟨by decide, by decide, shift143_2412, rfl⟩
def row143:OrdinaryBounds.Source 2412 2557:=
  ⟨src143,⟨Research6969.PackedRanks.TerminalRanks16To19.rank16 50419, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover143⟩⟩
end Research6969.OrdSource
end Z6969Source0921

-- Source: Research6969.OrdChecks001
section Z6969Source0922
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell55:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,27,some 35,385979,[OrdSource.row56],.marked⟩
theorem checked55:cell55.check OrdinaryBooks.near 351:=by decide +kernel
def cell56:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,21,some 26,385979,[OrdSource.row54],.marked⟩
theorem checked56:cell56.check OrdinaryBooks.near 351:=by decide +kernel
def cell57:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,15,some 20,385979,[OrdSource.row51],.marked⟩
theorem checked57:cell57.check OrdinaryBooks.near 351:=by decide +kernel
def cell58:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,13,some 14,385979,[OrdSource.row50],.surface⟩
theorem checked58:cell58.check OrdinaryBooks.near 351:=by decide +kernel
def cell59:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,10,some 12,385979,[OrdSource.row49],.surface⟩
theorem checked59:cell59.check OrdinaryBooks.near 351:=by decide +kernel
def cell60:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,6,some 9,385979,[],.surface⟩
theorem checked60:cell60.check OrdinaryBooks.near 351:=by decide +kernel
def cell61:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,3,some 5,385979,[],.surface⟩
theorem checked61:cell61.check OrdinaryBooks.near 351:=by decide +kernel
def cell62:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,1,some 2,385979,[],.surface⟩
theorem checked62:cell62.check OrdinaryBooks.near 351:=by decide +kernel
def cell63:OrdinaryCell.Row 2314 2411:=⟨22,22,9,3,0,some 0,385979,[],.ambient⟩
theorem checked63:cell63.check OrdinaryBooks.near 351:=by decide +kernel
def cell64:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,32769,none,514639,[OrdSource.row100],.marked⟩
theorem checked64:cell64.check OrdinaryBooks.near 351:=by decide +kernel
def cell65:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,16385,some 32768,514639,[OrdSource.row99],.marked⟩
theorem checked65:cell65.check OrdinaryBooks.near 351:=by decide +kernel
def cell66:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,8193,some 16384,514639,[OrdSource.row98],.marked⟩
theorem checked66:cell66.check OrdinaryBooks.near 351:=by decide +kernel
def cell67:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,4097,some 8192,514639,[OrdSource.row97],.marked⟩
theorem checked67:cell67.check OrdinaryBooks.near 351:=by decide +kernel
def cell68:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,2049,some 4096,514639,[OrdSource.row96],.marked⟩
theorem checked68:cell68.check OrdinaryBooks.near 351:=by decide +kernel
def cell69:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,1025,some 2048,514639,[OrdSource.row94,OrdSource.row95],.marked⟩
theorem checked69:cell69.check OrdinaryBooks.near 351:=by decide +kernel
def cell70:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,513,some 1024,514639,[OrdSource.row93],.marked⟩
theorem checked70:cell70.check OrdinaryBooks.near 351:=by decide +kernel
def cell71:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,257,some 512,514639,[OrdSource.row91],.marked⟩
theorem checked71:cell71.check OrdinaryBooks.near 351:=by decide +kernel
def cell72:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,161,some 256,514639,[OrdSource.row89],.marked⟩
theorem checked72:cell72.check OrdinaryBooks.near 351:=by decide +kernel
def cell73:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,97,some 160,514639,[OrdSource.row87],.marked⟩
theorem checked73:cell73.check OrdinaryBooks.near 351:=by decide +kernel
def cell74:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,65,some 96,514639,[OrdSource.row85],.marked⟩
theorem checked74:cell74.check OrdinaryBooks.near 351:=by decide +kernel
def cell75:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,48,some 64,514639,[OrdSource.row84],.marked⟩
theorem checked75:cell75.check OrdinaryBooks.near 351:=by decide +kernel
def cell76:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,36,some 47,514639,[OrdSource.row83],.marked⟩
theorem checked76:cell76.check OrdinaryBooks.near 351:=by decide +kernel
def cell77:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,27,some 35,514639,[OrdSource.row82],.marked⟩
theorem checked77:cell77.check OrdinaryBooks.near 351:=by decide +kernel
def cell78:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,21,some 26,514639,[OrdSource.row81],.marked⟩
theorem checked78:cell78.check OrdinaryBooks.near 351:=by decide +kernel
def cell79:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,15,some 20,514639,[OrdSource.row80],.marked⟩
theorem checked79:cell79.check OrdinaryBooks.near 351:=by decide +kernel
def cell80:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,10,some 14,514639,[OrdSource.row79],.marked⟩
theorem checked80:cell80.check OrdinaryBooks.near 351:=by decide +kernel
def cell81:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,6,some 9,514639,[OrdSource.row78],.surface⟩
theorem checked81:cell81.check OrdinaryBooks.near 351:=by decide +kernel
def cell82:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,3,some 5,514639,[OrdSource.row77],.surface⟩
theorem checked82:cell82.check OrdinaryBooks.near 351:=by decide +kernel
def cell83:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,1,some 2,514639,[OrdSource.row76],.surface⟩
theorem checked83:cell83.check OrdinaryBooks.near 351:=by decide +kernel
def cell84:OrdinaryCell.Row 2314 2411:=⟨22,22,9,4,0,some 0,514639,[],.ambient⟩
theorem checked84:cell84.check OrdinaryBooks.near 351:=by decide +kernel
def cell85:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,32769,none,643299,[OrdSource.row120],.marked⟩
theorem checked85:cell85.check OrdinaryBooks.near 351:=by decide +kernel
def cell86:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,16385,some 32768,643299,[OrdSource.row119],.marked⟩
theorem checked86:cell86.check OrdinaryBooks.near 351:=by decide +kernel
def cell87:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,8193,some 16384,643299,[OrdSource.row118],.marked⟩
theorem checked87:cell87.check OrdinaryBooks.near 351:=by decide +kernel
def cell88:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,4097,some 8192,643299,[OrdSource.row117],.marked⟩
theorem checked88:cell88.check OrdinaryBooks.near 351:=by decide +kernel
def cell89:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,1025,some 1536,643299,[OrdSource.row116],.marked⟩
theorem checked89:cell89.check OrdinaryBooks.near 351:=by decide +kernel
def cell90:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,513,some 1024,643299,[OrdSource.row115],.marked⟩
theorem checked90:cell90.check OrdinaryBooks.near 351:=by decide +kernel
def cell91:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,257,some 512,643299,[OrdSource.row113],.marked⟩
theorem checked91:cell91.check OrdinaryBooks.near 351:=by decide +kernel
def cell92:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,161,some 256,643299,[OrdSource.row112],.marked⟩
theorem checked92:cell92.check OrdinaryBooks.near 351:=by decide +kernel
def cell93:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,97,some 160,643299,[OrdSource.row111],.marked⟩
theorem checked93:cell93.check OrdinaryBooks.near 351:=by decide +kernel
def cell94:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,65,some 96,643299,[OrdSource.row110],.marked⟩
theorem checked94:cell94.check OrdinaryBooks.near 351:=by decide +kernel
def cell95:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,48,some 64,643299,[OrdSource.row109],.marked⟩
theorem checked95:cell95.check OrdinaryBooks.near 351:=by decide +kernel
def cell96:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,36,some 47,643299,[OrdSource.row108],.marked⟩
theorem checked96:cell96.check OrdinaryBooks.near 351:=by decide +kernel
def cell97:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,27,some 35,643299,[OrdSource.row107],.marked⟩
theorem checked97:cell97.check OrdinaryBooks.near 351:=by decide +kernel
def cell98:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,21,some 26,643299,[OrdSource.row106],.marked⟩
theorem checked98:cell98.check OrdinaryBooks.near 351:=by decide +kernel
def cell99:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,15,some 20,643299,[OrdSource.row105],.marked⟩
theorem checked99:cell99.check OrdinaryBooks.near 351:=by decide +kernel
def cell100:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,10,some 14,643299,[OrdSource.row104],.marked⟩
theorem checked100:cell100.check OrdinaryBooks.near 351:=by decide +kernel
def cell101:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,6,some 9,643299,[OrdSource.row103],.marked⟩
theorem checked101:cell101.check OrdinaryBooks.near 351:=by decide +kernel
def cell102:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,3,some 5,643299,[OrdSource.row102],.surface⟩
theorem checked102:cell102.check OrdinaryBooks.near 351:=by decide +kernel
def cell103:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,1,some 2,643299,[OrdSource.row101],.surface⟩
theorem checked103:cell103.check OrdinaryBooks.near 351:=by decide +kernel
def cell104:OrdinaryCell.Row 2314 2411:=⟨22,22,9,5,0,some 0,643299,[],.ambient⟩
theorem checked104:cell104.check OrdinaryBooks.near 351:=by decide +kernel
def cell105:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,1025,some 1536,771959,[OrdSource.row135],.marked⟩
theorem checked105:cell105.check OrdinaryBooks.near 351:=by decide +kernel
def cell106:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,513,some 1024,771959,[OrdSource.row134],.marked⟩
theorem checked106:cell106.check OrdinaryBooks.near 351:=by decide +kernel
def cell107:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,257,some 512,771959,[OrdSource.row133],.marked⟩
theorem checked107:cell107.check OrdinaryBooks.near 351:=by decide +kernel
def cell108:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,161,some 256,771959,[OrdSource.row132],.marked⟩
theorem checked108:cell108.check OrdinaryBooks.near 351:=by decide +kernel
def cell109:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,97,some 160,771959,[OrdSource.row131],.marked⟩
theorem checked109:cell109.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0922

-- Source: Research6969.OrdChecks002
section Z6969Source0923
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell110:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,65,some 96,771959,[OrdSource.row130],.marked⟩
theorem checked110:cell110.check OrdinaryBooks.near 351:=by decide +kernel
def cell111:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,48,some 64,771959,[OrdSource.row129],.marked⟩
theorem checked111:cell111.check OrdinaryBooks.near 351:=by decide +kernel
def cell112:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,36,some 47,771959,[OrdSource.row128],.marked⟩
theorem checked112:cell112.check OrdinaryBooks.near 351:=by decide +kernel
def cell113:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,27,some 35,771959,[OrdSource.row127],.marked⟩
theorem checked113:cell113.check OrdinaryBooks.near 351:=by decide +kernel
def cell114:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,21,some 26,771959,[OrdSource.row126],.marked⟩
theorem checked114:cell114.check OrdinaryBooks.near 351:=by decide +kernel
def cell115:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,15,some 20,771959,[OrdSource.row125],.marked⟩
theorem checked115:cell115.check OrdinaryBooks.near 351:=by decide +kernel
def cell116:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,10,some 14,771959,[OrdSource.row124],.marked⟩
theorem checked116:cell116.check OrdinaryBooks.near 351:=by decide +kernel
def cell117:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,6,some 9,771959,[OrdSource.row123],.marked⟩
theorem checked117:cell117.check OrdinaryBooks.near 351:=by decide +kernel
def cell118:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,3,some 5,771959,[OrdSource.row122],.surface⟩
theorem checked118:cell118.check OrdinaryBooks.near 351:=by decide +kernel
def cell119:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,1,some 2,771959,[OrdSource.row121],.surface⟩
theorem checked119:cell119.check OrdinaryBooks.near 351:=by decide +kernel
def cell120:OrdinaryCell.Row 2314 2411:=⟨22,22,9,6,0,some 0,771959,[],.ambient⟩
theorem checked120:cell120.check OrdinaryBooks.near 351:=by decide +kernel
def cell121:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,32769,none,128659,[OrdSource.row14],.excluded⟩
theorem checked121:cell121.check OrdinaryBooks.near 351:=by decide +kernel
def cell122:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,16385,some 32768,128659,[OrdSource.row13],.excluded⟩
theorem checked122:cell122.check OrdinaryBooks.near 351:=by decide +kernel
def cell123:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,8193,some 16384,128659,[OrdSource.row12],.excluded⟩
theorem checked123:cell123.check OrdinaryBooks.near 351:=by decide +kernel
def cell124:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,4097,some 8192,128659,[OrdSource.row11],.excluded⟩
theorem checked124:cell124.check OrdinaryBooks.near 351:=by decide +kernel
def cell125:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,2049,some 4096,128659,[OrdSource.row10],.excluded⟩
theorem checked125:cell125.check OrdinaryBooks.near 351:=by decide +kernel
def cell126:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,1025,some 2048,128659,[OrdSource.row9],.excluded⟩
theorem checked126:cell126.check OrdinaryBooks.near 351:=by decide +kernel
def cell127:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,513,some 1024,128659,[OrdSource.row7,OrdSource.row8],.excluded⟩
theorem checked127:cell127.check OrdinaryBooks.near 351:=by decide +kernel
def cell128:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,257,some 512,128659,[OrdSource.row6],.marked⟩
theorem checked128:cell128.check OrdinaryBooks.near 351:=by decide +kernel
def cell129:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,161,some 256,128659,[OrdSource.row5],.marked⟩
theorem checked129:cell129.check OrdinaryBooks.near 351:=by decide +kernel
def cell130:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,97,some 160,128659,[OrdSource.row4],.marked⟩
theorem checked130:cell130.check OrdinaryBooks.near 351:=by decide +kernel
def cell131:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,65,some 96,128659,[OrdSource.row3],.marked⟩
theorem checked131:cell131.check OrdinaryBooks.near 351:=by decide +kernel
def cell132:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,48,some 64,128659,[OrdSource.row2],.affine⟩
theorem checked132:cell132.check OrdinaryBooks.near 351:=by decide +kernel
def cell133:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,36,some 47,128659,[OrdSource.row0],.affine⟩
theorem checked133:cell133.check OrdinaryBooks.near 351:=by decide +kernel
def cell134:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,27,some 35,128659,[],.affine⟩
theorem checked134:cell134.check OrdinaryBooks.near 351:=by decide +kernel
def cell135:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,21,some 26,128659,[],.affine⟩
theorem checked135:cell135.check OrdinaryBooks.near 351:=by decide +kernel
def cell136:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,15,some 20,128659,[],.affine⟩
theorem checked136:cell136.check OrdinaryBooks.near 351:=by decide +kernel
def cell137:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,10,some 14,128659,[],.affine⟩
theorem checked137:cell137.check OrdinaryBooks.near 351:=by decide +kernel
def cell138:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,6,some 9,128659,[],.affine⟩
theorem checked138:cell138.check OrdinaryBooks.near 351:=by decide +kernel
def cell139:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,3,some 5,128659,[],.affine⟩
theorem checked139:cell139.check OrdinaryBooks.near 351:=by decide +kernel
def cell140:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,1,some 2,128659,[],.affine⟩
theorem checked140:cell140.check OrdinaryBooks.near 351:=by decide +kernel
def cell141:OrdinaryCell.Row 2314 2411:=⟨23,24,9,1,0,some 0,128659,[],.affine⟩
theorem checked141:cell141.check OrdinaryBooks.near 351:=by decide +kernel
def cell142:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,32769,none,257319,[OrdSource.row46],.excluded⟩
theorem checked142:cell142.check OrdinaryBooks.near 351:=by decide +kernel
def cell143:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,16385,some 32768,257319,[OrdSource.row45],.excluded⟩
theorem checked143:cell143.check OrdinaryBooks.near 351:=by decide +kernel
def cell144:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,8193,some 16384,257319,[OrdSource.row44],.excluded⟩
theorem checked144:cell144.check OrdinaryBooks.near 351:=by decide +kernel
def cell145:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,4097,some 8192,257319,[OrdSource.row43],.excluded⟩
theorem checked145:cell145.check OrdinaryBooks.near 351:=by decide +kernel
def cell146:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,2049,some 4096,257319,[OrdSource.row42],.excluded⟩
theorem checked146:cell146.check OrdinaryBooks.near 351:=by decide +kernel
def cell147:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,1025,some 2048,257319,[OrdSource.row40,OrdSource.row41],.excluded⟩
theorem checked147:cell147.check OrdinaryBooks.near 351:=by decide +kernel
def cell148:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,513,some 1024,257319,[OrdSource.row39],.marked⟩
theorem checked148:cell148.check OrdinaryBooks.near 351:=by decide +kernel
def cell149:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,257,some 512,257319,[OrdSource.row37,OrdSource.row38],.marked⟩
theorem checked149:cell149.check OrdinaryBooks.near 351:=by decide +kernel
def cell150:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,161,some 256,257319,[OrdSource.row36],.marked⟩
theorem checked150:cell150.check OrdinaryBooks.near 351:=by decide +kernel
def cell151:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,97,some 160,257319,[OrdSource.row33],.marked⟩
theorem checked151:cell151.check OrdinaryBooks.near 351:=by decide +kernel
def cell152:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,65,some 96,257319,[OrdSource.row30],.marked⟩
theorem checked152:cell152.check OrdinaryBooks.near 351:=by decide +kernel
def cell153:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,48,some 64,257319,[OrdSource.row23],.marked⟩
theorem checked153:cell153.check OrdinaryBooks.near 351:=by decide +kernel
def cell154:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,36,some 47,257319,[OrdSource.row19],.marked⟩
theorem checked154:cell154.check OrdinaryBooks.near 351:=by decide +kernel
def cell155:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,27,some 35,257319,[OrdSource.row15],(.node 8043223611471520 299354)⟩
theorem checked155:cell155.check OrdinaryBooks.near 351:=by decide +kernel
def cell156:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,27,some 35,299354,[OrdSource.row47],.marked⟩
theorem checked156:cell156.check OrdinaryBooks.near 351:=by decide +kernel
def cell157:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,21,some 26,257319,[],.surface⟩
theorem checked157:cell157.check OrdinaryBooks.near 351:=by decide +kernel
def cell158:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,15,some 20,257319,[],.surface⟩
theorem checked158:cell158.check OrdinaryBooks.near 351:=by decide +kernel
def cell159:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,10,some 14,257319,[],.surface⟩
theorem checked159:cell159.check OrdinaryBooks.near 351:=by decide +kernel
def cell160:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,6,some 9,257319,[],.surface⟩
theorem checked160:cell160.check OrdinaryBooks.near 351:=by decide +kernel
def cell161:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,3,some 5,257319,[],.surface⟩
theorem checked161:cell161.check OrdinaryBooks.near 351:=by decide +kernel
def cell162:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,1,some 2,257319,[],.surface⟩
theorem checked162:cell162.check OrdinaryBooks.near 351:=by decide +kernel
def cell163:OrdinaryCell.Row 2314 2411:=⟨23,24,9,2,0,some 0,257319,[],.ambient⟩
theorem checked163:cell163.check OrdinaryBooks.near 351:=by decide +kernel
def cell164:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,32769,none,385979,[OrdSource.row75],.excluded⟩
theorem checked164:cell164.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0923

end Merged_Z6969Pack0654

-- merged module Z6969Pack0655
section Merged_Z6969Pack0655

-- Source: Research6969.OrdPower00
section Z6969Source0924
set_option autoImplicit true
namespace Research6969.OrdPower
open PowerSheets PowerExclusion PhysicalWindow
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem shiftOrdPower0_2314 : Positive (entry 22 5 4 1537 643299) 2314 2411 := by decide +kernel
theorem covered0 : Cover (Positive (entry 22 5 4 1537 643299)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower0_2314, rfl⟩
private theorem shiftOrdPower1_2314 : Positive (entry 22 5 4 2049 643299) 2314 2411 := by decide +kernel
theorem covered1 : Cover (Positive (entry 22 5 4 2049 643299)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower1_2314, rfl⟩
private theorem shiftOrdPower2_2314 : Positive (entry 22 6 3 1537 771959) 2314 2411 := by decide +kernel
theorem covered2 : Cover (Positive (entry 22 6 3 1537 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower2_2314, rfl⟩
private theorem shiftOrdPower3_2314 : Positive (entry 22 6 3 2049 771959) 2314 2411 := by decide +kernel
theorem covered3 : Cover (Positive (entry 22 6 3 2049 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower3_2314, rfl⟩
private theorem shiftOrdPower4_2314 : Positive (entry 22 6 3 4097 771959) 2314 2411 := by decide +kernel
theorem covered4 : Cover (Positive (entry 22 6 3 4097 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower4_2314, rfl⟩
private theorem shiftOrdPower5_2314 : Positive (entry 22 6 3 8193 771959) 2314 2411 := by decide +kernel
theorem covered5 : Cover (Positive (entry 22 6 3 8193 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower5_2314, rfl⟩
end Research6969.OrdPower
end Z6969Source0924

-- Source: Research6969.OrdPower01
section Z6969Source0925
set_option autoImplicit true
namespace Research6969.OrdPower
open PowerSheets PowerExclusion PhysicalWindow
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem shiftOrdPower6_2314 : Positive (entry 22 6 3 16385 771959) 2314 2411 := by decide +kernel
theorem covered6 : Cover (Positive (entry 22 6 3 16385 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower6_2314, rfl⟩
private theorem shiftOrdPower7_2314 : Positive (entry 22 6 3 32769 771959) 2314 2411 := by decide +kernel
theorem covered7 : Cover (Positive (entry 22 6 3 32769 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower7_2314, rfl⟩
private theorem shiftOrdPower8_2314 : Positive (entry 23 5 4 1025 643299) 2314 2411 := by decide +kernel
theorem covered8 : Cover (Positive (entry 23 5 4 1025 643299)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower8_2314, rfl⟩
private theorem shiftOrdPower9_2314 : Positive (entry 23 5 4 2049 643299) 2314 2411 := by decide +kernel
theorem covered9 : Cover (Positive (entry 23 5 4 2049 643299)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower9_2314, rfl⟩
private theorem shiftOrdPower10_2314 : Positive (entry 23 6 3 1025 771959) 2314 2411 := by decide +kernel
theorem covered10 : Cover (Positive (entry 23 6 3 1025 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower10_2314, rfl⟩
private theorem shiftOrdPower11_2314 : Positive (entry 23 6 3 2049 771959) 2314 2411 := by decide +kernel
theorem covered11 : Cover (Positive (entry 23 6 3 2049 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower11_2314, rfl⟩
end Research6969.OrdPower
end Z6969Source0925

-- Source: Research6969.OrdRouteNear0
section Z6969Source0926
set_option autoImplicit true
namespace Research6969.OrdRouteNear0
open OrdinaryRoute
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000
private theorem leaf0:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,32769,none⟩:=
  plain OrdReceipts.cell0 OrdReceipts.checked0 (by decide) (by decide)
private theorem leaf1:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,16385,some 32768⟩:=
  plain OrdReceipts.cell1 OrdReceipts.checked1 (by decide) (by decide)
private theorem leaf2:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,8193,some 16384⟩:=
  plain OrdReceipts.cell2 OrdReceipts.checked2 (by decide) (by decide)
private theorem leaf3:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,4097,some 8192⟩:=
  plain OrdReceipts.cell3 OrdReceipts.checked3 (by decide) (by decide)
private theorem leaf4:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,2049,some 4096⟩:=
  plain OrdReceipts.cell4 OrdReceipts.checked4 (by decide) (by decide)
private theorem leaf5:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,1025,some 2048⟩:=
  plain OrdReceipts.cell5 OrdReceipts.checked5 (by decide) (by decide)
private theorem leaf6:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,513,some 1024⟩:=
  plain OrdReceipts.cell6 OrdReceipts.checked6 (by decide) (by decide)
private theorem leaf7:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,257,some 512⟩:=
  plain OrdReceipts.cell7 OrdReceipts.checked7 (by decide) (by decide)
private theorem leaf8:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,161,some 256⟩:=
  plain OrdReceipts.cell8 OrdReceipts.checked8 (by decide) (by decide)
private theorem leaf9:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,97,some 160⟩:=
  plain OrdReceipts.cell9 OrdReceipts.checked9 (by decide) (by decide)
private theorem leaf10:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,65,some 96⟩:=
  plain OrdReceipts.cell10 OrdReceipts.checked10 (by decide) (by decide)
private theorem leaf11:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,48,some 64⟩:=
  plain OrdReceipts.cell11 OrdReceipts.checked11 (by decide) (by decide)
private theorem leaf12:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,36,some 47⟩:=
  plain OrdReceipts.cell12 OrdReceipts.checked12 (by decide) (by decide)
private theorem leaf13:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,27,some 35⟩:=
  plain OrdReceipts.cell13 OrdReceipts.checked13 (by decide) (by decide)
private theorem leaf14:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,21,some 26⟩:=
  plain OrdReceipts.cell14 OrdReceipts.checked14 (by decide) (by decide)
private theorem leaf15:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,15,some 20⟩:=
  plain OrdReceipts.cell15 OrdReceipts.checked15 (by decide) (by decide)
private theorem leaf16:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,10,some 14⟩:=
  plain OrdReceipts.cell16 OrdReceipts.checked16 (by decide) (by decide)
private theorem leaf17:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,6,some 9⟩:=
  plain OrdReceipts.cell17 OrdReceipts.checked17 (by decide) (by decide)
private theorem leaf18:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,3,some 5⟩:=
  plain OrdReceipts.cell18 OrdReceipts.checked18 (by decide) (by decide)
private theorem leaf19:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,1,some 2⟩:=
  plain OrdReceipts.cell19 OrdReceipts.checked19 (by decide) (by decide)
private theorem leaf20:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,1,0,some 0⟩:=
  plain OrdReceipts.cell20 OrdReceipts.checked20 (by decide) (by decide)
private theorem leaf21:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,32769,none⟩:=
  plain OrdReceipts.cell21 OrdReceipts.checked21 (by decide) (by decide)
private theorem leaf22:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,16385,some 32768⟩:=
  plain OrdReceipts.cell22 OrdReceipts.checked22 (by decide) (by decide)
private theorem leaf23:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,8193,some 16384⟩:=
  plain OrdReceipts.cell23 OrdReceipts.checked23 (by decide) (by decide)
private theorem leaf24:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,4097,some 8192⟩:=
  plain OrdReceipts.cell24 OrdReceipts.checked24 (by decide) (by decide)
private theorem leaf25:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,2049,some 4096⟩:=
  plain OrdReceipts.cell25 OrdReceipts.checked25 (by decide) (by decide)
private theorem leaf26:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,1025,some 2048⟩:=
  plain OrdReceipts.cell26 OrdReceipts.checked26 (by decide) (by decide)
private theorem leaf27:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,513,some 1024⟩:=
  plain OrdReceipts.cell27 OrdReceipts.checked27 (by decide) (by decide)
private theorem leaf28:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,257,some 512⟩:=
  plain OrdReceipts.cell28 OrdReceipts.checked28 (by decide) (by decide)
private theorem leaf29:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,161,some 256⟩:=
  plain OrdReceipts.cell29 OrdReceipts.checked29 (by decide) (by decide)
private theorem leaf30:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,97,some 160⟩:=
  plain OrdReceipts.cell30 OrdReceipts.checked30 (by decide) (by decide)
private theorem leaf31:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,65,some 96⟩:=
  plain OrdReceipts.cell31 OrdReceipts.checked31 (by decide) (by decide)
private theorem leaf32:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,48,some 64⟩:=
  plain OrdReceipts.cell32 OrdReceipts.checked32 (by decide) (by decide)
private theorem leaf33:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,36,some 47⟩:=
  plain OrdReceipts.cell33 OrdReceipts.checked33 (by decide) (by decide)
private theorem leaf34:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,27,some 35⟩:=
  plain OrdReceipts.cell34 OrdReceipts.checked34 (by decide) (by decide)
private theorem leaf35:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,21,some 26⟩:=
  plain OrdReceipts.cell35 OrdReceipts.checked35 (by decide) (by decide)
private theorem leaf36:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,15,some 20⟩:=
  plain OrdReceipts.cell36 OrdReceipts.checked36 (by decide) (by decide)
private theorem leaf37:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,10,some 14⟩:=
  plain OrdReceipts.cell37 OrdReceipts.checked37 (by decide) (by decide)
private theorem leaf38:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,6,some 9⟩:=
  plain OrdReceipts.cell38 OrdReceipts.checked38 (by decide) (by decide)
private theorem leaf39:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,3,some 5⟩:=
  plain OrdReceipts.cell39 OrdReceipts.checked39 (by decide) (by decide)
private theorem leaf40:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,1,some 2⟩:=
  plain OrdReceipts.cell40 OrdReceipts.checked40 (by decide) (by decide)
private theorem leaf41:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,2,0,some 0⟩:=
  plain OrdReceipts.cell41 OrdReceipts.checked41 (by decide) (by decide)
private theorem leaf42:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,32769,none⟩:=
  plain OrdReceipts.cell42 OrdReceipts.checked42 (by decide) (by decide)
private theorem leaf43:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,16385,some 32768⟩:=
  plain OrdReceipts.cell43 OrdReceipts.checked43 (by decide) (by decide)
private theorem leaf44:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,8193,some 16384⟩:=
  plain OrdReceipts.cell44 OrdReceipts.checked44 (by decide) (by decide)
private theorem leaf45:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,4097,some 8192⟩:=
  plain OrdReceipts.cell45 OrdReceipts.checked45 (by decide) (by decide)
private theorem leaf46:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,2049,some 4096⟩:=
  plain OrdReceipts.cell46 OrdReceipts.checked46 (by decide) (by decide)
private theorem leaf47:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,1025,some 2048⟩:=
  plain OrdReceipts.cell47 OrdReceipts.checked47 (by decide) (by decide)
private theorem leaf48:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,513,some 1024⟩:=
  plain OrdReceipts.cell48 OrdReceipts.checked48 (by decide) (by decide)
private theorem leaf49:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,257,some 512⟩:=
  plain OrdReceipts.cell49 OrdReceipts.checked49 (by decide) (by decide)
private theorem leaf50:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,161,some 256⟩:=
  plain OrdReceipts.cell50 OrdReceipts.checked50 (by decide) (by decide)
private theorem leaf51:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,97,some 160⟩:=
  plain OrdReceipts.cell51 OrdReceipts.checked51 (by decide) (by decide)
private theorem leaf52:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,65,some 96⟩:=
  plain OrdReceipts.cell52 OrdReceipts.checked52 (by decide) (by decide)
private theorem leaf53:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,48,some 64⟩:=
  plain OrdReceipts.cell53 OrdReceipts.checked53 (by decide) (by decide)
private theorem leaf54:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,36,some 47⟩:=
  plain OrdReceipts.cell54 OrdReceipts.checked54 (by decide) (by decide)
private theorem leaf55:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,27,some 35⟩:=
  plain OrdReceipts.cell55 OrdReceipts.checked55 (by decide) (by decide)
private theorem leaf56:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,21,some 26⟩:=
  plain OrdReceipts.cell56 OrdReceipts.checked56 (by decide) (by decide)
private theorem leaf57:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,15,some 20⟩:=
  plain OrdReceipts.cell57 OrdReceipts.checked57 (by decide) (by decide)
private theorem leaf58:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,13,some 14⟩:=
  plain OrdReceipts.cell58 OrdReceipts.checked58 (by decide) (by decide)
private theorem leaf59:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,10,some 12⟩:=
  plain OrdReceipts.cell59 OrdReceipts.checked59 (by decide) (by decide)
private theorem leaf60:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,6,some 9⟩:=
  plain OrdReceipts.cell60 OrdReceipts.checked60 (by decide) (by decide)
private theorem leaf61:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,3,some 5⟩:=
  plain OrdReceipts.cell61 OrdReceipts.checked61 (by decide) (by decide)
private theorem leaf62:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,1,some 2⟩:=
  plain OrdReceipts.cell62 OrdReceipts.checked62 (by decide) (by decide)
private theorem leaf63:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,3,0,some 0⟩:=
  plain OrdReceipts.cell63 OrdReceipts.checked63 (by decide) (by decide)
private theorem leaf64:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,32769,none⟩:=
  plain OrdReceipts.cell64 OrdReceipts.checked64 (by decide) (by decide)
private theorem leaf65:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,16385,some 32768⟩:=
  plain OrdReceipts.cell65 OrdReceipts.checked65 (by decide) (by decide)
private theorem leaf66:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,8193,some 16384⟩:=
  plain OrdReceipts.cell66 OrdReceipts.checked66 (by decide) (by decide)
private theorem leaf67:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,4097,some 8192⟩:=
  plain OrdReceipts.cell67 OrdReceipts.checked67 (by decide) (by decide)
private theorem leaf68:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,2049,some 4096⟩:=
  plain OrdReceipts.cell68 OrdReceipts.checked68 (by decide) (by decide)
private theorem leaf69:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,1025,some 2048⟩:=
  plain OrdReceipts.cell69 OrdReceipts.checked69 (by decide) (by decide)
private theorem leaf70:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,513,some 1024⟩:=
  plain OrdReceipts.cell70 OrdReceipts.checked70 (by decide) (by decide)
private theorem leaf71:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,257,some 512⟩:=
  plain OrdReceipts.cell71 OrdReceipts.checked71 (by decide) (by decide)
private theorem leaf72:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,161,some 256⟩:=
  plain OrdReceipts.cell72 OrdReceipts.checked72 (by decide) (by decide)
private theorem leaf73:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,97,some 160⟩:=
  plain OrdReceipts.cell73 OrdReceipts.checked73 (by decide) (by decide)
private theorem leaf74:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,65,some 96⟩:=
  plain OrdReceipts.cell74 OrdReceipts.checked74 (by decide) (by decide)
private theorem leaf75:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,48,some 64⟩:=
  plain OrdReceipts.cell75 OrdReceipts.checked75 (by decide) (by decide)
private theorem leaf76:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,36,some 47⟩:=
  plain OrdReceipts.cell76 OrdReceipts.checked76 (by decide) (by decide)
private theorem leaf77:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,27,some 35⟩:=
  plain OrdReceipts.cell77 OrdReceipts.checked77 (by decide) (by decide)
private theorem leaf78:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,21,some 26⟩:=
  plain OrdReceipts.cell78 OrdReceipts.checked78 (by decide) (by decide)
private theorem leaf79:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,15,some 20⟩:=
  plain OrdReceipts.cell79 OrdReceipts.checked79 (by decide) (by decide)
private theorem leaf80:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,10,some 14⟩:=
  plain OrdReceipts.cell80 OrdReceipts.checked80 (by decide) (by decide)
private theorem leaf81:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,6,some 9⟩:=
  plain OrdReceipts.cell81 OrdReceipts.checked81 (by decide) (by decide)
private theorem leaf82:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,3,some 5⟩:=
  plain OrdReceipts.cell82 OrdReceipts.checked82 (by decide) (by decide)
private theorem leaf83:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,1,some 2⟩:=
  plain OrdReceipts.cell83 OrdReceipts.checked83 (by decide) (by decide)
private theorem leaf84:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,4,0,some 0⟩:=
  plain OrdReceipts.cell84 OrdReceipts.checked84 (by decide) (by decide)
private theorem leaf85:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,32769,none⟩:=
  plain OrdReceipts.cell85 OrdReceipts.checked85 (by decide) (by decide)
private theorem leaf86:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,16385,some 32768⟩:=
  plain OrdReceipts.cell86 OrdReceipts.checked86 (by decide) (by decide)
private theorem leaf87:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,8193,some 16384⟩:=
  plain OrdReceipts.cell87 OrdReceipts.checked87 (by decide) (by decide)
private theorem leaf88:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,4097,some 8192⟩:=
  plain OrdReceipts.cell88 OrdReceipts.checked88 (by decide) (by decide)
private theorem leaf89:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,2049,some 4096⟩:=
  power _ 643299 (by decide) OrdPower.covered1 (by decide) (by decide) (by decide)
private theorem leaf90:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,1537,some 2048⟩:=
  power _ 643299 (by decide) OrdPower.covered0 (by decide) (by decide) (by decide)
private theorem leaf91:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,1025,some 1536⟩:=
  plain OrdReceipts.cell89 OrdReceipts.checked89 (by decide) (by decide)
private theorem leaf92:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,513,some 1024⟩:=
  plain OrdReceipts.cell90 OrdReceipts.checked90 (by decide) (by decide)
private theorem leaf93:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,257,some 512⟩:=
  plain OrdReceipts.cell91 OrdReceipts.checked91 (by decide) (by decide)
private theorem leaf94:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,161,some 256⟩:=
  plain OrdReceipts.cell92 OrdReceipts.checked92 (by decide) (by decide)
private theorem leaf95:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,97,some 160⟩:=
  plain OrdReceipts.cell93 OrdReceipts.checked93 (by decide) (by decide)
private theorem leaf96:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,65,some 96⟩:=
  plain OrdReceipts.cell94 OrdReceipts.checked94 (by decide) (by decide)
private theorem leaf97:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,48,some 64⟩:=
  plain OrdReceipts.cell95 OrdReceipts.checked95 (by decide) (by decide)
private theorem leaf98:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,36,some 47⟩:=
  plain OrdReceipts.cell96 OrdReceipts.checked96 (by decide) (by decide)
private theorem leaf99:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,27,some 35⟩:=
  plain OrdReceipts.cell97 OrdReceipts.checked97 (by decide) (by decide)
private theorem leaf100:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,21,some 26⟩:=
  plain OrdReceipts.cell98 OrdReceipts.checked98 (by decide) (by decide)
private theorem leaf101:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,15,some 20⟩:=
  plain OrdReceipts.cell99 OrdReceipts.checked99 (by decide) (by decide)
private theorem leaf102:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,10,some 14⟩:=
  plain OrdReceipts.cell100 OrdReceipts.checked100 (by decide) (by decide)
private theorem leaf103:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,6,some 9⟩:=
  plain OrdReceipts.cell101 OrdReceipts.checked101 (by decide) (by decide)
private theorem leaf104:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,3,some 5⟩:=
  plain OrdReceipts.cell102 OrdReceipts.checked102 (by decide) (by decide)
private theorem leaf105:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,1,some 2⟩:=
  plain OrdReceipts.cell103 OrdReceipts.checked103 (by decide) (by decide)
private theorem leaf106:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,5,0,some 0⟩:=
  plain OrdReceipts.cell104 OrdReceipts.checked104 (by decide) (by decide)
private theorem leaf107:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,32769,none⟩:=
  power _ 771959 (by decide) OrdPower.covered7 (by decide) (by decide) (by decide)
private theorem leaf108:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,16385,some 32768⟩:=
  power _ 771959 (by decide) OrdPower.covered6 (by decide) (by decide) (by decide)
private theorem leaf109:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,8193,some 16384⟩:=
  power _ 771959 (by decide) OrdPower.covered5 (by decide) (by decide) (by decide)
private theorem leaf110:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,4097,some 8192⟩:=
  power _ 771959 (by decide) OrdPower.covered4 (by decide) (by decide) (by decide)
private theorem leaf111:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,2049,some 4096⟩:=
  power _ 771959 (by decide) OrdPower.covered3 (by decide) (by decide) (by decide)
private theorem leaf112:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,1537,some 2048⟩:=
  power _ 771959 (by decide) OrdPower.covered2 (by decide) (by decide) (by decide)
private theorem leaf113:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,1025,some 1536⟩:=
  plain OrdReceipts.cell105 OrdReceipts.checked105 (by decide) (by decide)
private theorem leaf114:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,513,some 1024⟩:=
  plain OrdReceipts.cell106 OrdReceipts.checked106 (by decide) (by decide)
private theorem leaf115:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,257,some 512⟩:=
  plain OrdReceipts.cell107 OrdReceipts.checked107 (by decide) (by decide)
private theorem leaf116:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,161,some 256⟩:=
  plain OrdReceipts.cell108 OrdReceipts.checked108 (by decide) (by decide)
private theorem leaf117:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,97,some 160⟩:=
  plain OrdReceipts.cell109 OrdReceipts.checked109 (by decide) (by decide)
private theorem leaf118:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,65,some 96⟩:=
  plain OrdReceipts.cell110 OrdReceipts.checked110 (by decide) (by decide)
private theorem leaf119:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,48,some 64⟩:=
  plain OrdReceipts.cell111 OrdReceipts.checked111 (by decide) (by decide)
private theorem leaf120:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,36,some 47⟩:=
  plain OrdReceipts.cell112 OrdReceipts.checked112 (by decide) (by decide)
private theorem leaf121:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,27,some 35⟩:=
  plain OrdReceipts.cell113 OrdReceipts.checked113 (by decide) (by decide)
private theorem leaf122:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,21,some 26⟩:=
  plain OrdReceipts.cell114 OrdReceipts.checked114 (by decide) (by decide)
private theorem leaf123:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,15,some 20⟩:=
  plain OrdReceipts.cell115 OrdReceipts.checked115 (by decide) (by decide)
private theorem leaf124:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,10,some 14⟩:=
  plain OrdReceipts.cell116 OrdReceipts.checked116 (by decide) (by decide)
private theorem leaf125:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,6,some 9⟩:=
  plain OrdReceipts.cell117 OrdReceipts.checked117 (by decide) (by decide)
private theorem leaf126:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,3,some 5⟩:=
  plain OrdReceipts.cell118 OrdReceipts.checked118 (by decide) (by decide)
private theorem leaf127:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,1,some 2⟩:=
  plain OrdReceipts.cell119 OrdReceipts.checked119 (by decide) (by decide)
private theorem leaf128:Done 2314 2411 OrdinaryBooks.near 351 ⟨22,22,9,6,0,some 0⟩:=
  plain OrdReceipts.cell120 OrdReceipts.checked120 (by decide) (by decide)
private theorem tail1_32769:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 32769:=leaf0
private theorem tail1_16385:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 16385:=join leaf1 tail1_32769
private theorem tail1_8193:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 8193:=join leaf2 tail1_16385
private theorem tail1_4097:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 4097:=join leaf3 tail1_8193
private theorem tail1_2049:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 2049:=join leaf4 tail1_4097
private theorem tail1_1025:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 1025:=join leaf5 tail1_2049
private theorem tail1_513:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 513:=join leaf6 tail1_1025
private theorem tail1_257:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 257:=join leaf7 tail1_513
private theorem tail1_161:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 161:=join leaf8 tail1_257
private theorem tail1_97:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 97:=join leaf9 tail1_161
private theorem tail1_65:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 65:=join leaf10 tail1_97
private theorem tail1_48:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 48:=join leaf11 tail1_65
private theorem tail1_36:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 36:=join leaf12 tail1_48
private theorem tail1_27:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 27:=join leaf13 tail1_36
private theorem tail1_21:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 21:=join leaf14 tail1_27
private theorem tail1_15:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 15:=join leaf15 tail1_21
private theorem tail1_10:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 10:=join leaf16 tail1_15
private theorem tail1_6:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 6:=join leaf17 tail1_10
private theorem tail1_3:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 3:=join leaf18 tail1_6
private theorem tail1_1:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 1:=join leaf19 tail1_3
private theorem tail1_0:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 1 0:=join leaf20 tail1_1
private theorem tail2_32769:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 32769:=leaf21
private theorem tail2_16385:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 16385:=join leaf22 tail2_32769
private theorem tail2_8193:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 8193:=join leaf23 tail2_16385
private theorem tail2_4097:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 4097:=join leaf24 tail2_8193
private theorem tail2_2049:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 2049:=join leaf25 tail2_4097
private theorem tail2_1025:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 1025:=join leaf26 tail2_2049
private theorem tail2_513:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 513:=join leaf27 tail2_1025
private theorem tail2_257:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 257:=join leaf28 tail2_513
private theorem tail2_161:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 161:=join leaf29 tail2_257
private theorem tail2_97:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 97:=join leaf30 tail2_161
private theorem tail2_65:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 65:=join leaf31 tail2_97
private theorem tail2_48:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 48:=join leaf32 tail2_65
private theorem tail2_36:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 36:=join leaf33 tail2_48
private theorem tail2_27:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 27:=join leaf34 tail2_36
private theorem tail2_21:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 21:=join leaf35 tail2_27
private theorem tail2_15:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 15:=join leaf36 tail2_21
private theorem tail2_10:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 10:=join leaf37 tail2_15
private theorem tail2_6:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 6:=join leaf38 tail2_10
private theorem tail2_3:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 3:=join leaf39 tail2_6
private theorem tail2_1:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 1:=join leaf40 tail2_3
private theorem tail2_0:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 2 0:=join leaf41 tail2_1
private theorem tail3_32769:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 32769:=leaf42
private theorem tail3_16385:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 16385:=join leaf43 tail3_32769
private theorem tail3_8193:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 8193:=join leaf44 tail3_16385
private theorem tail3_4097:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 4097:=join leaf45 tail3_8193
private theorem tail3_2049:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 2049:=join leaf46 tail3_4097
private theorem tail3_1025:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 1025:=join leaf47 tail3_2049
private theorem tail3_513:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 513:=join leaf48 tail3_1025
private theorem tail3_257:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 257:=join leaf49 tail3_513
private theorem tail3_161:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 161:=join leaf50 tail3_257
private theorem tail3_97:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 97:=join leaf51 tail3_161
private theorem tail3_65:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 65:=join leaf52 tail3_97
private theorem tail3_48:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 48:=join leaf53 tail3_65
private theorem tail3_36:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 36:=join leaf54 tail3_48
private theorem tail3_27:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 27:=join leaf55 tail3_36
private theorem tail3_21:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 21:=join leaf56 tail3_27
private theorem tail3_15:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 15:=join leaf57 tail3_21
private theorem tail3_13:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 13:=join leaf58 tail3_15
private theorem tail3_10:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 10:=join leaf59 tail3_13
private theorem tail3_6:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 6:=join leaf60 tail3_10
private theorem tail3_3:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 3:=join leaf61 tail3_6
private theorem tail3_1:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 1:=join leaf62 tail3_3
private theorem tail3_0:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 3 0:=join leaf63 tail3_1
private theorem tail4_32769:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 32769:=leaf64
private theorem tail4_16385:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 16385:=join leaf65 tail4_32769
private theorem tail4_8193:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 8193:=join leaf66 tail4_16385
private theorem tail4_4097:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 4097:=join leaf67 tail4_8193
private theorem tail4_2049:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 2049:=join leaf68 tail4_4097
private theorem tail4_1025:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 1025:=join leaf69 tail4_2049
private theorem tail4_513:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 513:=join leaf70 tail4_1025
private theorem tail4_257:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 257:=join leaf71 tail4_513
private theorem tail4_161:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 161:=join leaf72 tail4_257
private theorem tail4_97:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 97:=join leaf73 tail4_161
private theorem tail4_65:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 65:=join leaf74 tail4_97
private theorem tail4_48:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 48:=join leaf75 tail4_65
private theorem tail4_36:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 36:=join leaf76 tail4_48
private theorem tail4_27:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 27:=join leaf77 tail4_36
private theorem tail4_21:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 21:=join leaf78 tail4_27
private theorem tail4_15:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 15:=join leaf79 tail4_21
private theorem tail4_10:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 10:=join leaf80 tail4_15
private theorem tail4_6:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 6:=join leaf81 tail4_10
private theorem tail4_3:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 3:=join leaf82 tail4_6
private theorem tail4_1:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 1:=join leaf83 tail4_3
private theorem tail4_0:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 4 0:=join leaf84 tail4_1
private theorem tail5_32769:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 32769:=leaf85
private theorem tail5_16385:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 16385:=join leaf86 tail5_32769
private theorem tail5_8193:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 8193:=join leaf87 tail5_16385
private theorem tail5_4097:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 4097:=join leaf88 tail5_8193
private theorem tail5_2049:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 2049:=join leaf89 tail5_4097
private theorem tail5_1537:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 1537:=join leaf90 tail5_2049
private theorem tail5_1025:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 1025:=join leaf91 tail5_1537
private theorem tail5_513:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 513:=join leaf92 tail5_1025
private theorem tail5_257:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 257:=join leaf93 tail5_513
private theorem tail5_161:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 161:=join leaf94 tail5_257
private theorem tail5_97:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 97:=join leaf95 tail5_161
private theorem tail5_65:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 65:=join leaf96 tail5_97
private theorem tail5_48:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 48:=join leaf97 tail5_65
private theorem tail5_36:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 36:=join leaf98 tail5_48
private theorem tail5_27:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 27:=join leaf99 tail5_36
private theorem tail5_21:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 21:=join leaf100 tail5_27
private theorem tail5_15:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 15:=join leaf101 tail5_21
private theorem tail5_10:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 10:=join leaf102 tail5_15
private theorem tail5_6:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 6:=join leaf103 tail5_10
private theorem tail5_3:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 3:=join leaf104 tail5_6
private theorem tail5_1:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 1:=join leaf105 tail5_3
private theorem tail5_0:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 5 0:=join leaf106 tail5_1
private theorem tail6_32769:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 32769:=leaf107
private theorem tail6_16385:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 16385:=join leaf108 tail6_32769
private theorem tail6_8193:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 8193:=join leaf109 tail6_16385
private theorem tail6_4097:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 4097:=join leaf110 tail6_8193
private theorem tail6_2049:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 2049:=join leaf111 tail6_4097
private theorem tail6_1537:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 1537:=join leaf112 tail6_2049
private theorem tail6_1025:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 1025:=join leaf113 tail6_1537
private theorem tail6_513:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 513:=join leaf114 tail6_1025
private theorem tail6_257:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 257:=join leaf115 tail6_513
private theorem tail6_161:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 161:=join leaf116 tail6_257
private theorem tail6_97:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 97:=join leaf117 tail6_161
private theorem tail6_65:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 65:=join leaf118 tail6_97
private theorem tail6_48:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 48:=join leaf119 tail6_65
private theorem tail6_36:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 36:=join leaf120 tail6_48
private theorem tail6_27:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 27:=join leaf121 tail6_36
private theorem tail6_21:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 21:=join leaf122 tail6_27
private theorem tail6_15:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 15:=join leaf123 tail6_21
private theorem tail6_10:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 10:=join leaf124 tail6_15
private theorem tail6_6:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 6:=join leaf125 tail6_10
private theorem tail6_3:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 3:=join leaf126 tail6_6
private theorem tail6_1:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 1:=join leaf127 tail6_3
private theorem tail6_0:Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 6 0:=join leaf128 tail6_1
theorem allDegrees (a:ℕ) (lo:0<a) (hi:a≤6):
    Tail 2314 2411 OrdinaryBooks.near 351 22 22 9 a 0:=by
  interval_cases a
  · exact tail1_0
  · exact tail2_0
  · exact tail3_0
  · exact tail4_0
  · exact tail5_0
  · exact tail6_0
end Research6969.OrdRouteNear0
end Z6969Source0926

-- Source: Research6969.OrdChecks003
section Z6969Source0927
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell165:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,16385,some 32768,385979,[OrdSource.row74],.excluded⟩
theorem checked165:cell165.check OrdinaryBooks.near 351:=by decide +kernel
def cell166:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,8193,some 16384,385979,[OrdSource.row73],.excluded⟩
theorem checked166:cell166.check OrdinaryBooks.near 351:=by decide +kernel
def cell167:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,4097,some 8192,385979,[OrdSource.row72],.excluded⟩
theorem checked167:cell167.check OrdinaryBooks.near 351:=by decide +kernel
def cell168:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,2049,some 4096,385979,[OrdSource.row71],.marked⟩
theorem checked168:cell168.check OrdinaryBooks.near 351:=by decide +kernel
def cell169:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,1025,some 2048,385979,[OrdSource.row69,OrdSource.row70],.marked⟩
theorem checked169:cell169.check OrdinaryBooks.near 351:=by decide +kernel
def cell170:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,513,some 1024,385979,[OrdSource.row68],.marked⟩
theorem checked170:cell170.check OrdinaryBooks.near 351:=by decide +kernel
def cell171:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,257,some 512,385979,[OrdSource.row66,OrdSource.row67],.marked⟩
theorem checked171:cell171.check OrdinaryBooks.near 351:=by decide +kernel
def cell172:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,161,some 256,385979,[OrdSource.row65],.marked⟩
theorem checked172:cell172.check OrdinaryBooks.near 351:=by decide +kernel
def cell173:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,97,some 160,385979,[OrdSource.row64],.marked⟩
theorem checked173:cell173.check OrdinaryBooks.near 351:=by decide +kernel
def cell174:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,65,some 96,385979,[OrdSource.row62],.marked⟩
theorem checked174:cell174.check OrdinaryBooks.near 351:=by decide +kernel
def cell175:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,48,some 64,385979,[OrdSource.row60],.marked⟩
theorem checked175:cell175.check OrdinaryBooks.near 351:=by decide +kernel
def cell176:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,36,some 47,385979,[OrdSource.row58],.marked⟩
theorem checked176:cell176.check OrdinaryBooks.near 351:=by decide +kernel
def cell177:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,27,some 35,385979,[OrdSource.row56],.marked⟩
theorem checked177:cell177.check OrdinaryBooks.near 351:=by decide +kernel
def cell178:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,21,some 26,385979,[OrdSource.row54],.marked⟩
theorem checked178:cell178.check OrdinaryBooks.near 351:=by decide +kernel
def cell179:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,18,some 20,385979,[OrdSource.row53],.marked⟩
theorem checked179:cell179.check OrdinaryBooks.near 351:=by decide +kernel
def cell180:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,17,some 17,385979,[OrdSource.row52],.surface⟩
theorem checked180:cell180.check OrdinaryBooks.near 351:=by decide +kernel
def cell181:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,15,some 16,385979,[OrdSource.row51],.surface⟩
theorem checked181:cell181.check OrdinaryBooks.near 351:=by decide +kernel
def cell182:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,13,some 14,385979,[OrdSource.row50],.surface⟩
theorem checked182:cell182.check OrdinaryBooks.near 351:=by decide +kernel
def cell183:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,10,some 12,385979,[OrdSource.row49],.surface⟩
theorem checked183:cell183.check OrdinaryBooks.near 351:=by decide +kernel
def cell184:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,6,some 9,385979,[],.surface⟩
theorem checked184:cell184.check OrdinaryBooks.near 351:=by decide +kernel
def cell185:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,3,some 5,385979,[],.surface⟩
theorem checked185:cell185.check OrdinaryBooks.near 351:=by decide +kernel
def cell186:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,1,some 2,385979,[],.surface⟩
theorem checked186:cell186.check OrdinaryBooks.near 351:=by decide +kernel
def cell187:OrdinaryCell.Row 2314 2411:=⟨23,24,9,3,0,some 0,385979,[],.ambient⟩
theorem checked187:cell187.check OrdinaryBooks.near 351:=by decide +kernel
def cell188:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,32769,none,514639,[OrdSource.row100],.marked⟩
theorem checked188:cell188.check OrdinaryBooks.near 351:=by decide +kernel
def cell189:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,16385,some 32768,514639,[OrdSource.row99],.marked⟩
theorem checked189:cell189.check OrdinaryBooks.near 351:=by decide +kernel
def cell190:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,8193,some 16384,514639,[OrdSource.row98],.marked⟩
theorem checked190:cell190.check OrdinaryBooks.near 351:=by decide +kernel
def cell191:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,4097,some 8192,514639,[OrdSource.row97],.marked⟩
theorem checked191:cell191.check OrdinaryBooks.near 351:=by decide +kernel
def cell192:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,2049,some 4096,514639,[OrdSource.row96],.marked⟩
theorem checked192:cell192.check OrdinaryBooks.near 351:=by decide +kernel
def cell193:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,1025,some 2048,514639,[OrdSource.row94,OrdSource.row95],.marked⟩
theorem checked193:cell193.check OrdinaryBooks.near 351:=by decide +kernel
def cell194:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,513,some 1024,514639,[OrdSource.row92,OrdSource.row93],.marked⟩
theorem checked194:cell194.check OrdinaryBooks.near 351:=by decide +kernel
def cell195:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,257,some 512,514639,[OrdSource.row91],.marked⟩
theorem checked195:cell195.check OrdinaryBooks.near 351:=by decide +kernel
def cell196:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,161,some 256,514639,[OrdSource.row89],.marked⟩
theorem checked196:cell196.check OrdinaryBooks.near 351:=by decide +kernel
def cell197:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,97,some 160,514639,[OrdSource.row87],.marked⟩
theorem checked197:cell197.check OrdinaryBooks.near 351:=by decide +kernel
def cell198:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,65,some 96,514639,[OrdSource.row85],.marked⟩
theorem checked198:cell198.check OrdinaryBooks.near 351:=by decide +kernel
def cell199:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,48,some 64,514639,[OrdSource.row84],.marked⟩
theorem checked199:cell199.check OrdinaryBooks.near 351:=by decide +kernel
def cell200:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,36,some 47,514639,[OrdSource.row83],.marked⟩
theorem checked200:cell200.check OrdinaryBooks.near 351:=by decide +kernel
def cell201:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,27,some 35,514639,[OrdSource.row82],.marked⟩
theorem checked201:cell201.check OrdinaryBooks.near 351:=by decide +kernel
def cell202:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,21,some 26,514639,[OrdSource.row81],.marked⟩
theorem checked202:cell202.check OrdinaryBooks.near 351:=by decide +kernel
def cell203:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,15,some 20,514639,[OrdSource.row80],.marked⟩
theorem checked203:cell203.check OrdinaryBooks.near 351:=by decide +kernel
def cell204:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,10,some 14,514639,[OrdSource.row79],.marked⟩
theorem checked204:cell204.check OrdinaryBooks.near 351:=by decide +kernel
def cell205:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,6,some 9,514639,[OrdSource.row78],.surface⟩
theorem checked205:cell205.check OrdinaryBooks.near 351:=by decide +kernel
def cell206:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,3,some 5,514639,[OrdSource.row77],.surface⟩
theorem checked206:cell206.check OrdinaryBooks.near 351:=by decide +kernel
def cell207:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,1,some 2,514639,[OrdSource.row76],.surface⟩
theorem checked207:cell207.check OrdinaryBooks.near 351:=by decide +kernel
def cell208:OrdinaryCell.Row 2314 2411:=⟨23,24,9,4,0,some 0,514639,[],.ambient⟩
theorem checked208:cell208.check OrdinaryBooks.near 351:=by decide +kernel
def cell209:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,32769,none,643299,[OrdSource.row120],.marked⟩
theorem checked209:cell209.check OrdinaryBooks.near 351:=by decide +kernel
def cell210:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,16385,some 32768,643299,[OrdSource.row119],.marked⟩
theorem checked210:cell210.check OrdinaryBooks.near 351:=by decide +kernel
def cell211:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,8193,some 16384,643299,[OrdSource.row118],.marked⟩
theorem checked211:cell211.check OrdinaryBooks.near 351:=by decide +kernel
def cell212:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,4097,some 8192,643299,[OrdSource.row117],.marked⟩
theorem checked212:cell212.check OrdinaryBooks.near 351:=by decide +kernel
def cell213:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,513,some 1024,643299,[OrdSource.row115],.marked⟩
theorem checked213:cell213.check OrdinaryBooks.near 351:=by decide +kernel
def cell214:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,257,some 512,643299,[OrdSource.row113],.marked⟩
theorem checked214:cell214.check OrdinaryBooks.near 351:=by decide +kernel
def cell215:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,161,some 256,643299,[OrdSource.row112],.marked⟩
theorem checked215:cell215.check OrdinaryBooks.near 351:=by decide +kernel
def cell216:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,97,some 160,643299,[OrdSource.row111],.marked⟩
theorem checked216:cell216.check OrdinaryBooks.near 351:=by decide +kernel
def cell217:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,65,some 96,643299,[OrdSource.row110],.marked⟩
theorem checked217:cell217.check OrdinaryBooks.near 351:=by decide +kernel
def cell218:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,48,some 64,643299,[OrdSource.row109],.marked⟩
theorem checked218:cell218.check OrdinaryBooks.near 351:=by decide +kernel
def cell219:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,36,some 47,643299,[OrdSource.row108],.marked⟩
theorem checked219:cell219.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0927

-- Source: Research6969.OrdChecks004
section Z6969Source0928
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell220:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,27,some 35,643299,[OrdSource.row107],.marked⟩
theorem checked220:cell220.check OrdinaryBooks.near 351:=by decide +kernel
def cell221:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,21,some 26,643299,[OrdSource.row106],.marked⟩
theorem checked221:cell221.check OrdinaryBooks.near 351:=by decide +kernel
def cell222:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,15,some 20,643299,[OrdSource.row105],.marked⟩
theorem checked222:cell222.check OrdinaryBooks.near 351:=by decide +kernel
def cell223:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,10,some 14,643299,[OrdSource.row104],.marked⟩
theorem checked223:cell223.check OrdinaryBooks.near 351:=by decide +kernel
def cell224:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,6,some 9,643299,[OrdSource.row103],.marked⟩
theorem checked224:cell224.check OrdinaryBooks.near 351:=by decide +kernel
def cell225:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,3,some 5,643299,[OrdSource.row102],.surface⟩
theorem checked225:cell225.check OrdinaryBooks.near 351:=by decide +kernel
def cell226:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,1,some 2,643299,[OrdSource.row101],.surface⟩
theorem checked226:cell226.check OrdinaryBooks.near 351:=by decide +kernel
def cell227:OrdinaryCell.Row 2314 2411:=⟨23,24,9,5,0,some 0,643299,[],.ambient⟩
theorem checked227:cell227.check OrdinaryBooks.near 351:=by decide +kernel
def cell228:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,513,some 1024,771959,[OrdSource.row134],.marked⟩
theorem checked228:cell228.check OrdinaryBooks.near 351:=by decide +kernel
def cell229:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,257,some 512,771959,[OrdSource.row133],.marked⟩
theorem checked229:cell229.check OrdinaryBooks.near 351:=by decide +kernel
def cell230:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,161,some 256,771959,[OrdSource.row132],.marked⟩
theorem checked230:cell230.check OrdinaryBooks.near 351:=by decide +kernel
def cell231:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,97,some 160,771959,[OrdSource.row131],.marked⟩
theorem checked231:cell231.check OrdinaryBooks.near 351:=by decide +kernel
def cell232:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,65,some 96,771959,[OrdSource.row130],.marked⟩
theorem checked232:cell232.check OrdinaryBooks.near 351:=by decide +kernel
def cell233:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,48,some 64,771959,[OrdSource.row129],.marked⟩
theorem checked233:cell233.check OrdinaryBooks.near 351:=by decide +kernel
def cell234:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,36,some 47,771959,[OrdSource.row128],.marked⟩
theorem checked234:cell234.check OrdinaryBooks.near 351:=by decide +kernel
def cell235:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,27,some 35,771959,[OrdSource.row127],.marked⟩
theorem checked235:cell235.check OrdinaryBooks.near 351:=by decide +kernel
def cell236:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,21,some 26,771959,[OrdSource.row126],.marked⟩
theorem checked236:cell236.check OrdinaryBooks.near 351:=by decide +kernel
def cell237:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,15,some 20,771959,[OrdSource.row125],.marked⟩
theorem checked237:cell237.check OrdinaryBooks.near 351:=by decide +kernel
def cell238:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,10,some 14,771959,[OrdSource.row124],.marked⟩
theorem checked238:cell238.check OrdinaryBooks.near 351:=by decide +kernel
def cell239:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,6,some 9,771959,[OrdSource.row123],.marked⟩
theorem checked239:cell239.check OrdinaryBooks.near 351:=by decide +kernel
def cell240:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,3,some 5,771959,[OrdSource.row122],.surface⟩
theorem checked240:cell240.check OrdinaryBooks.near 351:=by decide +kernel
def cell241:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,1,some 2,771959,[OrdSource.row121],.surface⟩
theorem checked241:cell241.check OrdinaryBooks.near 351:=by decide +kernel
def cell242:OrdinaryCell.Row 2314 2411:=⟨23,24,9,6,0,some 0,771959,[],.ambient⟩
theorem checked242:cell242.check OrdinaryBooks.near 351:=by decide +kernel
def cell243:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,32769,none,128659,[OrdSource.row14],.excluded⟩
theorem checked243:cell243.check OrdinaryBooks.near 351:=by decide +kernel
def cell244:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,16385,some 32768,128659,[OrdSource.row13],.excluded⟩
theorem checked244:cell244.check OrdinaryBooks.near 351:=by decide +kernel
def cell245:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,8193,some 16384,128659,[OrdSource.row12],.excluded⟩
theorem checked245:cell245.check OrdinaryBooks.near 351:=by decide +kernel
def cell246:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,4097,some 8192,128659,[OrdSource.row11],.excluded⟩
theorem checked246:cell246.check OrdinaryBooks.near 351:=by decide +kernel
def cell247:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,2049,some 4096,128659,[OrdSource.row10],.excluded⟩
theorem checked247:cell247.check OrdinaryBooks.near 351:=by decide +kernel
def cell248:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,1025,some 2048,128659,[OrdSource.row9],.excluded⟩
theorem checked248:cell248.check OrdinaryBooks.near 351:=by decide +kernel
def cell249:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,513,some 1024,128659,[OrdSource.row7,OrdSource.row8],.excluded⟩
theorem checked249:cell249.check OrdinaryBooks.near 351:=by decide +kernel
def cell250:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,257,some 512,128659,[OrdSource.row6],.excluded⟩
theorem checked250:cell250.check OrdinaryBooks.near 351:=by decide +kernel
def cell251:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,161,some 256,128659,[OrdSource.row5],.marked⟩
theorem checked251:cell251.check OrdinaryBooks.near 351:=by decide +kernel
def cell252:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,97,some 160,128659,[OrdSource.row4],.marked⟩
theorem checked252:cell252.check OrdinaryBooks.near 351:=by decide +kernel
def cell253:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,65,some 96,128659,[OrdSource.row3],.affine⟩
theorem checked253:cell253.check OrdinaryBooks.near 351:=by decide +kernel
def cell254:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,48,some 64,128659,[OrdSource.row2],.affine⟩
theorem checked254:cell254.check OrdinaryBooks.near 351:=by decide +kernel
def cell255:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,36,some 47,128659,[OrdSource.row0],.affine⟩
theorem checked255:cell255.check OrdinaryBooks.near 351:=by decide +kernel
def cell256:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,27,some 35,128659,[],.affine⟩
theorem checked256:cell256.check OrdinaryBooks.near 351:=by decide +kernel
def cell257:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,21,some 26,128659,[],.affine⟩
theorem checked257:cell257.check OrdinaryBooks.near 351:=by decide +kernel
def cell258:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,15,some 20,128659,[],.affine⟩
theorem checked258:cell258.check OrdinaryBooks.near 351:=by decide +kernel
def cell259:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,10,some 14,128659,[],.affine⟩
theorem checked259:cell259.check OrdinaryBooks.near 351:=by decide +kernel
def cell260:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,6,some 9,128659,[],.affine⟩
theorem checked260:cell260.check OrdinaryBooks.near 351:=by decide +kernel
def cell261:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,3,some 5,128659,[],.affine⟩
theorem checked261:cell261.check OrdinaryBooks.near 351:=by decide +kernel
def cell262:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,1,some 2,128659,[],.affine⟩
theorem checked262:cell262.check OrdinaryBooks.near 351:=by decide +kernel
def cell263:OrdinaryCell.Row 2314 2411:=⟨25,27,9,1,0,some 0,128659,[],.affine⟩
theorem checked263:cell263.check OrdinaryBooks.near 351:=by decide +kernel
def cell264:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,32769,none,257319,[OrdSource.row46],.excluded⟩
theorem checked264:cell264.check OrdinaryBooks.near 351:=by decide +kernel
def cell265:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,16385,some 32768,257319,[OrdSource.row45],.excluded⟩
theorem checked265:cell265.check OrdinaryBooks.near 351:=by decide +kernel
def cell266:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,8193,some 16384,257319,[OrdSource.row44],.excluded⟩
theorem checked266:cell266.check OrdinaryBooks.near 351:=by decide +kernel
def cell267:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,4097,some 8192,257319,[OrdSource.row43],.excluded⟩
theorem checked267:cell267.check OrdinaryBooks.near 351:=by decide +kernel
def cell268:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,2049,some 4096,257319,[OrdSource.row42],.excluded⟩
theorem checked268:cell268.check OrdinaryBooks.near 351:=by decide +kernel
def cell269:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,1025,some 2048,257319,[OrdSource.row40,OrdSource.row41],.excluded⟩
theorem checked269:cell269.check OrdinaryBooks.near 351:=by decide +kernel
def cell270:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,513,some 1024,257319,[OrdSource.row39],.excluded⟩
theorem checked270:cell270.check OrdinaryBooks.near 351:=by decide +kernel
def cell271:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,257,some 512,257319,[OrdSource.row37,OrdSource.row38],.marked⟩
theorem checked271:cell271.check OrdinaryBooks.near 351:=by decide +kernel
def cell272:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,161,some 256,257319,[OrdSource.row36],.marked⟩
theorem checked272:cell272.check OrdinaryBooks.near 351:=by decide +kernel
def cell273:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,97,some 160,257319,[OrdSource.row33],.marked⟩
theorem checked273:cell273.check OrdinaryBooks.near 351:=by decide +kernel
def cell274:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,65,some 96,257319,[OrdSource.row30],.marked⟩
theorem checked274:cell274.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0928

-- Source: Research6969.OrdPower02
section Z6969Source0929
set_option autoImplicit true
namespace Research6969.OrdPower
open PowerSheets PowerExclusion PhysicalWindow
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem shiftOrdPower12_2314 : Positive (entry 23 6 3 4097 771959) 2314 2411 := by decide +kernel
theorem covered12 : Cover (Positive (entry 23 6 3 4097 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower12_2314, rfl⟩
private theorem shiftOrdPower13_2314 : Positive (entry 23 6 3 8193 771959) 2314 2411 := by decide +kernel
theorem covered13 : Cover (Positive (entry 23 6 3 8193 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower13_2314, rfl⟩
private theorem shiftOrdPower14_2314 : Positive (entry 23 6 3 16385 771959) 2314 2411 := by decide +kernel
theorem covered14 : Cover (Positive (entry 23 6 3 16385 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower14_2314, rfl⟩
private theorem shiftOrdPower15_2314 : Positive (entry 23 6 3 32769 771959) 2314 2411 := by decide +kernel
theorem covered15 : Cover (Positive (entry 23 6 3 32769 771959)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower15_2314, rfl⟩
private theorem shiftOrdPower16_2314 : Positive (entry 25 5 4 1025 643299) 2314 2411 := by decide +kernel
theorem covered16 : Cover (Positive (entry 25 5 4 1025 643299)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower16_2314, rfl⟩
private theorem shiftOrdPower17_2314 : Positive (entry 25 5 4 2049 643299) 2314 2411 := by decide +kernel
theorem covered17 : Cover (Positive (entry 25 5 4 2049 643299)) 2411 2314 [2411] :=
  ⟨by decide, by decide, shiftOrdPower17_2314, rfl⟩
end Research6969.OrdPower
end Z6969Source0929

-- Source: Research6969.OrdRouteNear1
section Z6969Source0930
set_option autoImplicit true
namespace Research6969.OrdRouteNear1
open OrdinaryRoute
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000
private theorem leaf129:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,32769,none⟩:=
  plain OrdReceipts.cell121 OrdReceipts.checked121 (by decide) (by decide)
private theorem leaf130:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,16385,some 32768⟩:=
  plain OrdReceipts.cell122 OrdReceipts.checked122 (by decide) (by decide)
private theorem leaf131:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,8193,some 16384⟩:=
  plain OrdReceipts.cell123 OrdReceipts.checked123 (by decide) (by decide)
private theorem leaf132:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,4097,some 8192⟩:=
  plain OrdReceipts.cell124 OrdReceipts.checked124 (by decide) (by decide)
private theorem leaf133:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,2049,some 4096⟩:=
  plain OrdReceipts.cell125 OrdReceipts.checked125 (by decide) (by decide)
private theorem leaf134:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,1025,some 2048⟩:=
  plain OrdReceipts.cell126 OrdReceipts.checked126 (by decide) (by decide)
private theorem leaf135:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,513,some 1024⟩:=
  plain OrdReceipts.cell127 OrdReceipts.checked127 (by decide) (by decide)
private theorem leaf136:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,257,some 512⟩:=
  plain OrdReceipts.cell128 OrdReceipts.checked128 (by decide) (by decide)
private theorem leaf137:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,161,some 256⟩:=
  plain OrdReceipts.cell129 OrdReceipts.checked129 (by decide) (by decide)
private theorem leaf138:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,97,some 160⟩:=
  plain OrdReceipts.cell130 OrdReceipts.checked130 (by decide) (by decide)
private theorem leaf139:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,65,some 96⟩:=
  plain OrdReceipts.cell131 OrdReceipts.checked131 (by decide) (by decide)
private theorem leaf140:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,48,some 64⟩:=
  plain OrdReceipts.cell132 OrdReceipts.checked132 (by decide) (by decide)
private theorem leaf141:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,36,some 47⟩:=
  plain OrdReceipts.cell133 OrdReceipts.checked133 (by decide) (by decide)
private theorem leaf142:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,27,some 35⟩:=
  plain OrdReceipts.cell134 OrdReceipts.checked134 (by decide) (by decide)
private theorem leaf143:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,21,some 26⟩:=
  plain OrdReceipts.cell135 OrdReceipts.checked135 (by decide) (by decide)
private theorem leaf144:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,15,some 20⟩:=
  plain OrdReceipts.cell136 OrdReceipts.checked136 (by decide) (by decide)
private theorem leaf145:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,10,some 14⟩:=
  plain OrdReceipts.cell137 OrdReceipts.checked137 (by decide) (by decide)
private theorem leaf146:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,6,some 9⟩:=
  plain OrdReceipts.cell138 OrdReceipts.checked138 (by decide) (by decide)
private theorem leaf147:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,3,some 5⟩:=
  plain OrdReceipts.cell139 OrdReceipts.checked139 (by decide) (by decide)
private theorem leaf148:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,1,some 2⟩:=
  plain OrdReceipts.cell140 OrdReceipts.checked140 (by decide) (by decide)
private theorem leaf149:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,1,0,some 0⟩:=
  plain OrdReceipts.cell141 OrdReceipts.checked141 (by decide) (by decide)
private theorem leaf150:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,32769,none⟩:=
  plain OrdReceipts.cell142 OrdReceipts.checked142 (by decide) (by decide)
private theorem leaf151:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,16385,some 32768⟩:=
  plain OrdReceipts.cell143 OrdReceipts.checked143 (by decide) (by decide)
private theorem leaf152:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,8193,some 16384⟩:=
  plain OrdReceipts.cell144 OrdReceipts.checked144 (by decide) (by decide)
private theorem leaf153:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,4097,some 8192⟩:=
  plain OrdReceipts.cell145 OrdReceipts.checked145 (by decide) (by decide)
private theorem leaf154:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,2049,some 4096⟩:=
  plain OrdReceipts.cell146 OrdReceipts.checked146 (by decide) (by decide)
private theorem leaf155:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,1025,some 2048⟩:=
  plain OrdReceipts.cell147 OrdReceipts.checked147 (by decide) (by decide)
private theorem leaf156:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,513,some 1024⟩:=
  plain OrdReceipts.cell148 OrdReceipts.checked148 (by decide) (by decide)
private theorem leaf157:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,257,some 512⟩:=
  plain OrdReceipts.cell149 OrdReceipts.checked149 (by decide) (by decide)
private theorem leaf158:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,161,some 256⟩:=
  plain OrdReceipts.cell150 OrdReceipts.checked150 (by decide) (by decide)
private theorem leaf159:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,97,some 160⟩:=
  plain OrdReceipts.cell151 OrdReceipts.checked151 (by decide) (by decide)
private theorem leaf160:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,65,some 96⟩:=
  plain OrdReceipts.cell152 OrdReceipts.checked152 (by decide) (by decide)
private theorem leaf161:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,48,some 64⟩:=
  plain OrdReceipts.cell153 OrdReceipts.checked153 (by decide) (by decide)
private theorem leaf162:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,36,some 47⟩:=
  plain OrdReceipts.cell154 OrdReceipts.checked154 (by decide) (by decide)
private theorem leaf163:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,27,some 35⟩:=
  physical OrdReceipts.cell155 OrdReceipts.cell156 OrdReceipts.checked155 OrdReceipts.checked156 rfl 299354 (by decide) (by decide) (by decide) (by decide)
private theorem leaf164:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,21,some 26⟩:=
  plain OrdReceipts.cell157 OrdReceipts.checked157 (by decide) (by decide)
private theorem leaf165:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,15,some 20⟩:=
  plain OrdReceipts.cell158 OrdReceipts.checked158 (by decide) (by decide)
private theorem leaf166:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,10,some 14⟩:=
  plain OrdReceipts.cell159 OrdReceipts.checked159 (by decide) (by decide)
private theorem leaf167:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,6,some 9⟩:=
  plain OrdReceipts.cell160 OrdReceipts.checked160 (by decide) (by decide)
private theorem leaf168:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,3,some 5⟩:=
  plain OrdReceipts.cell161 OrdReceipts.checked161 (by decide) (by decide)
private theorem leaf169:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,1,some 2⟩:=
  plain OrdReceipts.cell162 OrdReceipts.checked162 (by decide) (by decide)
private theorem leaf170:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,2,0,some 0⟩:=
  plain OrdReceipts.cell163 OrdReceipts.checked163 (by decide) (by decide)
private theorem leaf171:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,32769,none⟩:=
  plain OrdReceipts.cell164 OrdReceipts.checked164 (by decide) (by decide)
private theorem leaf172:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,16385,some 32768⟩:=
  plain OrdReceipts.cell165 OrdReceipts.checked165 (by decide) (by decide)
private theorem leaf173:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,8193,some 16384⟩:=
  plain OrdReceipts.cell166 OrdReceipts.checked166 (by decide) (by decide)
private theorem leaf174:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,4097,some 8192⟩:=
  plain OrdReceipts.cell167 OrdReceipts.checked167 (by decide) (by decide)
private theorem leaf175:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,2049,some 4096⟩:=
  plain OrdReceipts.cell168 OrdReceipts.checked168 (by decide) (by decide)
private theorem leaf176:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,1025,some 2048⟩:=
  plain OrdReceipts.cell169 OrdReceipts.checked169 (by decide) (by decide)
private theorem leaf177:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,513,some 1024⟩:=
  plain OrdReceipts.cell170 OrdReceipts.checked170 (by decide) (by decide)
private theorem leaf178:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,257,some 512⟩:=
  plain OrdReceipts.cell171 OrdReceipts.checked171 (by decide) (by decide)
private theorem leaf179:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,161,some 256⟩:=
  plain OrdReceipts.cell172 OrdReceipts.checked172 (by decide) (by decide)
private theorem leaf180:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,97,some 160⟩:=
  plain OrdReceipts.cell173 OrdReceipts.checked173 (by decide) (by decide)
private theorem leaf181:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,65,some 96⟩:=
  plain OrdReceipts.cell174 OrdReceipts.checked174 (by decide) (by decide)
private theorem leaf182:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,48,some 64⟩:=
  plain OrdReceipts.cell175 OrdReceipts.checked175 (by decide) (by decide)
private theorem leaf183:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,36,some 47⟩:=
  plain OrdReceipts.cell176 OrdReceipts.checked176 (by decide) (by decide)
private theorem leaf184:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,27,some 35⟩:=
  plain OrdReceipts.cell177 OrdReceipts.checked177 (by decide) (by decide)
private theorem leaf185:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,21,some 26⟩:=
  plain OrdReceipts.cell178 OrdReceipts.checked178 (by decide) (by decide)
private theorem leaf186:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,18,some 20⟩:=
  plain OrdReceipts.cell179 OrdReceipts.checked179 (by decide) (by decide)
private theorem leaf187:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,17,some 17⟩:=
  plain OrdReceipts.cell180 OrdReceipts.checked180 (by decide) (by decide)
private theorem leaf188:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,15,some 16⟩:=
  plain OrdReceipts.cell181 OrdReceipts.checked181 (by decide) (by decide)
private theorem leaf189:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,13,some 14⟩:=
  plain OrdReceipts.cell182 OrdReceipts.checked182 (by decide) (by decide)
private theorem leaf190:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,10,some 12⟩:=
  plain OrdReceipts.cell183 OrdReceipts.checked183 (by decide) (by decide)
private theorem leaf191:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,6,some 9⟩:=
  plain OrdReceipts.cell184 OrdReceipts.checked184 (by decide) (by decide)
private theorem leaf192:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,3,some 5⟩:=
  plain OrdReceipts.cell185 OrdReceipts.checked185 (by decide) (by decide)
private theorem leaf193:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,1,some 2⟩:=
  plain OrdReceipts.cell186 OrdReceipts.checked186 (by decide) (by decide)
private theorem leaf194:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,3,0,some 0⟩:=
  plain OrdReceipts.cell187 OrdReceipts.checked187 (by decide) (by decide)
private theorem leaf195:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,32769,none⟩:=
  plain OrdReceipts.cell188 OrdReceipts.checked188 (by decide) (by decide)
private theorem leaf196:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,16385,some 32768⟩:=
  plain OrdReceipts.cell189 OrdReceipts.checked189 (by decide) (by decide)
private theorem leaf197:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,8193,some 16384⟩:=
  plain OrdReceipts.cell190 OrdReceipts.checked190 (by decide) (by decide)
private theorem leaf198:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,4097,some 8192⟩:=
  plain OrdReceipts.cell191 OrdReceipts.checked191 (by decide) (by decide)
private theorem leaf199:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,2049,some 4096⟩:=
  plain OrdReceipts.cell192 OrdReceipts.checked192 (by decide) (by decide)
private theorem leaf200:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,1025,some 2048⟩:=
  plain OrdReceipts.cell193 OrdReceipts.checked193 (by decide) (by decide)
private theorem leaf201:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,513,some 1024⟩:=
  plain OrdReceipts.cell194 OrdReceipts.checked194 (by decide) (by decide)
private theorem leaf202:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,257,some 512⟩:=
  plain OrdReceipts.cell195 OrdReceipts.checked195 (by decide) (by decide)
private theorem leaf203:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,161,some 256⟩:=
  plain OrdReceipts.cell196 OrdReceipts.checked196 (by decide) (by decide)
private theorem leaf204:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,97,some 160⟩:=
  plain OrdReceipts.cell197 OrdReceipts.checked197 (by decide) (by decide)
private theorem leaf205:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,65,some 96⟩:=
  plain OrdReceipts.cell198 OrdReceipts.checked198 (by decide) (by decide)
private theorem leaf206:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,48,some 64⟩:=
  plain OrdReceipts.cell199 OrdReceipts.checked199 (by decide) (by decide)
private theorem leaf207:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,36,some 47⟩:=
  plain OrdReceipts.cell200 OrdReceipts.checked200 (by decide) (by decide)
private theorem leaf208:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,27,some 35⟩:=
  plain OrdReceipts.cell201 OrdReceipts.checked201 (by decide) (by decide)
private theorem leaf209:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,21,some 26⟩:=
  plain OrdReceipts.cell202 OrdReceipts.checked202 (by decide) (by decide)
private theorem leaf210:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,15,some 20⟩:=
  plain OrdReceipts.cell203 OrdReceipts.checked203 (by decide) (by decide)
private theorem leaf211:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,10,some 14⟩:=
  plain OrdReceipts.cell204 OrdReceipts.checked204 (by decide) (by decide)
private theorem leaf212:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,6,some 9⟩:=
  plain OrdReceipts.cell205 OrdReceipts.checked205 (by decide) (by decide)
private theorem leaf213:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,3,some 5⟩:=
  plain OrdReceipts.cell206 OrdReceipts.checked206 (by decide) (by decide)
private theorem leaf214:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,1,some 2⟩:=
  plain OrdReceipts.cell207 OrdReceipts.checked207 (by decide) (by decide)
private theorem leaf215:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,4,0,some 0⟩:=
  plain OrdReceipts.cell208 OrdReceipts.checked208 (by decide) (by decide)
private theorem leaf216:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,32769,none⟩:=
  plain OrdReceipts.cell209 OrdReceipts.checked209 (by decide) (by decide)
private theorem leaf217:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,16385,some 32768⟩:=
  plain OrdReceipts.cell210 OrdReceipts.checked210 (by decide) (by decide)
private theorem leaf218:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,8193,some 16384⟩:=
  plain OrdReceipts.cell211 OrdReceipts.checked211 (by decide) (by decide)
private theorem leaf219:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,4097,some 8192⟩:=
  plain OrdReceipts.cell212 OrdReceipts.checked212 (by decide) (by decide)
private theorem leaf220:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,2049,some 4096⟩:=
  power _ 643299 (by decide) OrdPower.covered9 (by decide) (by decide) (by decide)
private theorem leaf221:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,1025,some 2048⟩:=
  power _ 643299 (by decide) OrdPower.covered8 (by decide) (by decide) (by decide)
private theorem leaf222:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,513,some 1024⟩:=
  plain OrdReceipts.cell213 OrdReceipts.checked213 (by decide) (by decide)
private theorem leaf223:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,257,some 512⟩:=
  plain OrdReceipts.cell214 OrdReceipts.checked214 (by decide) (by decide)
private theorem leaf224:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,161,some 256⟩:=
  plain OrdReceipts.cell215 OrdReceipts.checked215 (by decide) (by decide)
private theorem leaf225:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,97,some 160⟩:=
  plain OrdReceipts.cell216 OrdReceipts.checked216 (by decide) (by decide)
private theorem leaf226:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,65,some 96⟩:=
  plain OrdReceipts.cell217 OrdReceipts.checked217 (by decide) (by decide)
private theorem leaf227:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,48,some 64⟩:=
  plain OrdReceipts.cell218 OrdReceipts.checked218 (by decide) (by decide)
private theorem leaf228:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,36,some 47⟩:=
  plain OrdReceipts.cell219 OrdReceipts.checked219 (by decide) (by decide)
private theorem leaf229:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,27,some 35⟩:=
  plain OrdReceipts.cell220 OrdReceipts.checked220 (by decide) (by decide)
private theorem leaf230:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,21,some 26⟩:=
  plain OrdReceipts.cell221 OrdReceipts.checked221 (by decide) (by decide)
private theorem leaf231:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,15,some 20⟩:=
  plain OrdReceipts.cell222 OrdReceipts.checked222 (by decide) (by decide)
private theorem leaf232:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,10,some 14⟩:=
  plain OrdReceipts.cell223 OrdReceipts.checked223 (by decide) (by decide)
private theorem leaf233:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,6,some 9⟩:=
  plain OrdReceipts.cell224 OrdReceipts.checked224 (by decide) (by decide)
private theorem leaf234:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,3,some 5⟩:=
  plain OrdReceipts.cell225 OrdReceipts.checked225 (by decide) (by decide)
private theorem leaf235:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,1,some 2⟩:=
  plain OrdReceipts.cell226 OrdReceipts.checked226 (by decide) (by decide)
private theorem leaf236:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,5,0,some 0⟩:=
  plain OrdReceipts.cell227 OrdReceipts.checked227 (by decide) (by decide)
private theorem leaf237:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,32769,none⟩:=
  power _ 771959 (by decide) OrdPower.covered15 (by decide) (by decide) (by decide)
private theorem leaf238:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,16385,some 32768⟩:=
  power _ 771959 (by decide) OrdPower.covered14 (by decide) (by decide) (by decide)
private theorem leaf239:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,8193,some 16384⟩:=
  power _ 771959 (by decide) OrdPower.covered13 (by decide) (by decide) (by decide)
private theorem leaf240:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,4097,some 8192⟩:=
  power _ 771959 (by decide) OrdPower.covered12 (by decide) (by decide) (by decide)
private theorem leaf241:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,2049,some 4096⟩:=
  power _ 771959 (by decide) OrdPower.covered11 (by decide) (by decide) (by decide)
private theorem leaf242:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,1025,some 2048⟩:=
  power _ 771959 (by decide) OrdPower.covered10 (by decide) (by decide) (by decide)
private theorem leaf243:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,513,some 1024⟩:=
  plain OrdReceipts.cell228 OrdReceipts.checked228 (by decide) (by decide)
private theorem leaf244:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,257,some 512⟩:=
  plain OrdReceipts.cell229 OrdReceipts.checked229 (by decide) (by decide)
private theorem leaf245:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,161,some 256⟩:=
  plain OrdReceipts.cell230 OrdReceipts.checked230 (by decide) (by decide)
private theorem leaf246:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,97,some 160⟩:=
  plain OrdReceipts.cell231 OrdReceipts.checked231 (by decide) (by decide)
private theorem leaf247:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,65,some 96⟩:=
  plain OrdReceipts.cell232 OrdReceipts.checked232 (by decide) (by decide)
private theorem leaf248:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,48,some 64⟩:=
  plain OrdReceipts.cell233 OrdReceipts.checked233 (by decide) (by decide)
private theorem leaf249:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,36,some 47⟩:=
  plain OrdReceipts.cell234 OrdReceipts.checked234 (by decide) (by decide)
private theorem leaf250:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,27,some 35⟩:=
  plain OrdReceipts.cell235 OrdReceipts.checked235 (by decide) (by decide)
private theorem leaf251:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,21,some 26⟩:=
  plain OrdReceipts.cell236 OrdReceipts.checked236 (by decide) (by decide)
private theorem leaf252:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,15,some 20⟩:=
  plain OrdReceipts.cell237 OrdReceipts.checked237 (by decide) (by decide)
private theorem leaf253:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,10,some 14⟩:=
  plain OrdReceipts.cell238 OrdReceipts.checked238 (by decide) (by decide)
private theorem leaf254:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,6,some 9⟩:=
  plain OrdReceipts.cell239 OrdReceipts.checked239 (by decide) (by decide)
private theorem leaf255:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,3,some 5⟩:=
  plain OrdReceipts.cell240 OrdReceipts.checked240 (by decide) (by decide)
private theorem leaf256:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,1,some 2⟩:=
  plain OrdReceipts.cell241 OrdReceipts.checked241 (by decide) (by decide)
private theorem leaf257:Done 2314 2411 OrdinaryBooks.near 351 ⟨23,24,9,6,0,some 0⟩:=
  plain OrdReceipts.cell242 OrdReceipts.checked242 (by decide) (by decide)
private theorem tail1_32769:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 32769:=leaf129
private theorem tail1_16385:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 16385:=join leaf130 tail1_32769
private theorem tail1_8193:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 8193:=join leaf131 tail1_16385
private theorem tail1_4097:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 4097:=join leaf132 tail1_8193
private theorem tail1_2049:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 2049:=join leaf133 tail1_4097
private theorem tail1_1025:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 1025:=join leaf134 tail1_2049
private theorem tail1_513:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 513:=join leaf135 tail1_1025
private theorem tail1_257:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 257:=join leaf136 tail1_513
private theorem tail1_161:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 161:=join leaf137 tail1_257
private theorem tail1_97:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 97:=join leaf138 tail1_161
private theorem tail1_65:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 65:=join leaf139 tail1_97
private theorem tail1_48:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 48:=join leaf140 tail1_65
private theorem tail1_36:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 36:=join leaf141 tail1_48
private theorem tail1_27:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 27:=join leaf142 tail1_36
private theorem tail1_21:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 21:=join leaf143 tail1_27
private theorem tail1_15:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 15:=join leaf144 tail1_21
private theorem tail1_10:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 10:=join leaf145 tail1_15
private theorem tail1_6:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 6:=join leaf146 tail1_10
private theorem tail1_3:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 3:=join leaf147 tail1_6
private theorem tail1_1:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 1:=join leaf148 tail1_3
private theorem tail1_0:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 1 0:=join leaf149 tail1_1
private theorem tail2_32769:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 32769:=leaf150
private theorem tail2_16385:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 16385:=join leaf151 tail2_32769
private theorem tail2_8193:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 8193:=join leaf152 tail2_16385
private theorem tail2_4097:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 4097:=join leaf153 tail2_8193
private theorem tail2_2049:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 2049:=join leaf154 tail2_4097
private theorem tail2_1025:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 1025:=join leaf155 tail2_2049
private theorem tail2_513:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 513:=join leaf156 tail2_1025
private theorem tail2_257:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 257:=join leaf157 tail2_513
private theorem tail2_161:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 161:=join leaf158 tail2_257
private theorem tail2_97:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 97:=join leaf159 tail2_161
private theorem tail2_65:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 65:=join leaf160 tail2_97
private theorem tail2_48:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 48:=join leaf161 tail2_65
private theorem tail2_36:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 36:=join leaf162 tail2_48
private theorem tail2_27:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 27:=join leaf163 tail2_36
private theorem tail2_21:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 21:=join leaf164 tail2_27
private theorem tail2_15:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 15:=join leaf165 tail2_21
private theorem tail2_10:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 10:=join leaf166 tail2_15
private theorem tail2_6:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 6:=join leaf167 tail2_10
private theorem tail2_3:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 3:=join leaf168 tail2_6
private theorem tail2_1:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 1:=join leaf169 tail2_3
private theorem tail2_0:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 2 0:=join leaf170 tail2_1
private theorem tail3_32769:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 32769:=leaf171
private theorem tail3_16385:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 16385:=join leaf172 tail3_32769
private theorem tail3_8193:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 8193:=join leaf173 tail3_16385
private theorem tail3_4097:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 4097:=join leaf174 tail3_8193
private theorem tail3_2049:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 2049:=join leaf175 tail3_4097
private theorem tail3_1025:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 1025:=join leaf176 tail3_2049
private theorem tail3_513:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 513:=join leaf177 tail3_1025
private theorem tail3_257:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 257:=join leaf178 tail3_513
private theorem tail3_161:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 161:=join leaf179 tail3_257
private theorem tail3_97:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 97:=join leaf180 tail3_161
private theorem tail3_65:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 65:=join leaf181 tail3_97
private theorem tail3_48:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 48:=join leaf182 tail3_65
private theorem tail3_36:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 36:=join leaf183 tail3_48
private theorem tail3_27:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 27:=join leaf184 tail3_36
private theorem tail3_21:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 21:=join leaf185 tail3_27
private theorem tail3_18:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 18:=join leaf186 tail3_21
private theorem tail3_17:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 17:=join leaf187 tail3_18
private theorem tail3_15:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 15:=join leaf188 tail3_17
private theorem tail3_13:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 13:=join leaf189 tail3_15
private theorem tail3_10:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 10:=join leaf190 tail3_13
private theorem tail3_6:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 6:=join leaf191 tail3_10
private theorem tail3_3:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 3:=join leaf192 tail3_6
private theorem tail3_1:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 1:=join leaf193 tail3_3
private theorem tail3_0:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 3 0:=join leaf194 tail3_1
private theorem tail4_32769:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 32769:=leaf195
private theorem tail4_16385:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 16385:=join leaf196 tail4_32769
private theorem tail4_8193:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 8193:=join leaf197 tail4_16385
private theorem tail4_4097:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 4097:=join leaf198 tail4_8193
private theorem tail4_2049:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 2049:=join leaf199 tail4_4097
private theorem tail4_1025:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 1025:=join leaf200 tail4_2049
private theorem tail4_513:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 513:=join leaf201 tail4_1025
private theorem tail4_257:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 257:=join leaf202 tail4_513
private theorem tail4_161:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 161:=join leaf203 tail4_257
private theorem tail4_97:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 97:=join leaf204 tail4_161
private theorem tail4_65:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 65:=join leaf205 tail4_97
private theorem tail4_48:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 48:=join leaf206 tail4_65
private theorem tail4_36:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 36:=join leaf207 tail4_48
private theorem tail4_27:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 27:=join leaf208 tail4_36
private theorem tail4_21:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 21:=join leaf209 tail4_27
private theorem tail4_15:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 15:=join leaf210 tail4_21
private theorem tail4_10:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 10:=join leaf211 tail4_15
private theorem tail4_6:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 6:=join leaf212 tail4_10
private theorem tail4_3:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 3:=join leaf213 tail4_6
private theorem tail4_1:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 1:=join leaf214 tail4_3
private theorem tail4_0:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 4 0:=join leaf215 tail4_1
private theorem tail5_32769:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 32769:=leaf216
private theorem tail5_16385:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 16385:=join leaf217 tail5_32769
private theorem tail5_8193:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 8193:=join leaf218 tail5_16385
private theorem tail5_4097:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 4097:=join leaf219 tail5_8193
private theorem tail5_2049:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 2049:=join leaf220 tail5_4097
private theorem tail5_1025:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 1025:=join leaf221 tail5_2049
private theorem tail5_513:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 513:=join leaf222 tail5_1025
private theorem tail5_257:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 257:=join leaf223 tail5_513
private theorem tail5_161:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 161:=join leaf224 tail5_257
private theorem tail5_97:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 97:=join leaf225 tail5_161
private theorem tail5_65:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 65:=join leaf226 tail5_97
private theorem tail5_48:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 48:=join leaf227 tail5_65
private theorem tail5_36:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 36:=join leaf228 tail5_48
private theorem tail5_27:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 27:=join leaf229 tail5_36
private theorem tail5_21:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 21:=join leaf230 tail5_27
private theorem tail5_15:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 15:=join leaf231 tail5_21
private theorem tail5_10:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 10:=join leaf232 tail5_15
private theorem tail5_6:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 6:=join leaf233 tail5_10
private theorem tail5_3:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 3:=join leaf234 tail5_6
private theorem tail5_1:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 1:=join leaf235 tail5_3
private theorem tail5_0:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 5 0:=join leaf236 tail5_1
private theorem tail6_32769:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 32769:=leaf237
private theorem tail6_16385:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 16385:=join leaf238 tail6_32769
private theorem tail6_8193:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 8193:=join leaf239 tail6_16385
private theorem tail6_4097:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 4097:=join leaf240 tail6_8193
private theorem tail6_2049:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 2049:=join leaf241 tail6_4097
private theorem tail6_1025:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 1025:=join leaf242 tail6_2049
private theorem tail6_513:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 513:=join leaf243 tail6_1025
private theorem tail6_257:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 257:=join leaf244 tail6_513
private theorem tail6_161:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 161:=join leaf245 tail6_257
private theorem tail6_97:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 97:=join leaf246 tail6_161
private theorem tail6_65:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 65:=join leaf247 tail6_97
private theorem tail6_48:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 48:=join leaf248 tail6_65
private theorem tail6_36:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 36:=join leaf249 tail6_48
private theorem tail6_27:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 27:=join leaf250 tail6_36
private theorem tail6_21:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 21:=join leaf251 tail6_27
private theorem tail6_15:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 15:=join leaf252 tail6_21
private theorem tail6_10:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 10:=join leaf253 tail6_15
private theorem tail6_6:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 6:=join leaf254 tail6_10
private theorem tail6_3:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 3:=join leaf255 tail6_6
private theorem tail6_1:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 1:=join leaf256 tail6_3
private theorem tail6_0:Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 6 0:=join leaf257 tail6_1
theorem allDegrees (a:ℕ) (lo:0<a) (hi:a≤6):
    Tail 2314 2411 OrdinaryBooks.near 351 23 24 9 a 0:=by
  interval_cases a
  · exact tail1_0
  · exact tail2_0
  · exact tail3_0
  · exact tail4_0
  · exact tail5_0
  · exact tail6_0
end Research6969.OrdRouteNear1
end Z6969Source0930

-- Source: Research6969.OrdChecks005
section Z6969Source0931
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell275:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,48,some 64,257319,[OrdSource.row23],.marked⟩
theorem checked275:cell275.check OrdinaryBooks.near 351:=by decide +kernel
def cell276:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,36,some 47,257319,[OrdSource.row19],.marked⟩
theorem checked276:cell276.check OrdinaryBooks.near 351:=by decide +kernel
def cell277:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,27,some 35,257319,[OrdSource.row15],(.node 8043223611471520 299354)⟩
theorem checked277:cell277.check OrdinaryBooks.near 351:=by decide +kernel
def cell278:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,27,some 35,299354,[OrdSource.row47],.surface⟩
theorem checked278:cell278.check OrdinaryBooks.near 351:=by decide +kernel
def cell279:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,21,some 26,257319,[],.surface⟩
theorem checked279:cell279.check OrdinaryBooks.near 351:=by decide +kernel
def cell280:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,15,some 20,257319,[],.surface⟩
theorem checked280:cell280.check OrdinaryBooks.near 351:=by decide +kernel
def cell281:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,10,some 14,257319,[],.surface⟩
theorem checked281:cell281.check OrdinaryBooks.near 351:=by decide +kernel
def cell282:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,6,some 9,257319,[],.surface⟩
theorem checked282:cell282.check OrdinaryBooks.near 351:=by decide +kernel
def cell283:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,3,some 5,257319,[],.surface⟩
theorem checked283:cell283.check OrdinaryBooks.near 351:=by decide +kernel
def cell284:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,1,some 2,257319,[],.surface⟩
theorem checked284:cell284.check OrdinaryBooks.near 351:=by decide +kernel
def cell285:OrdinaryCell.Row 2314 2411:=⟨25,27,9,2,0,some 0,257319,[],.ambient⟩
theorem checked285:cell285.check OrdinaryBooks.near 351:=by decide +kernel
def cell286:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,32769,none,385979,[OrdSource.row75],.excluded⟩
theorem checked286:cell286.check OrdinaryBooks.near 351:=by decide +kernel
def cell287:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,16385,some 32768,385979,[OrdSource.row74],.excluded⟩
theorem checked287:cell287.check OrdinaryBooks.near 351:=by decide +kernel
def cell288:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,8193,some 16384,385979,[OrdSource.row73],.excluded⟩
theorem checked288:cell288.check OrdinaryBooks.near 351:=by decide +kernel
def cell289:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,4097,some 8192,385979,[OrdSource.row72],.excluded⟩
theorem checked289:cell289.check OrdinaryBooks.near 351:=by decide +kernel
def cell290:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,2049,some 4096,385979,[OrdSource.row71],.excluded⟩
theorem checked290:cell290.check OrdinaryBooks.near 351:=by decide +kernel
def cell291:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,1025,some 2048,385979,[OrdSource.row69,OrdSource.row70],.excluded⟩
theorem checked291:cell291.check OrdinaryBooks.near 351:=by decide +kernel
def cell292:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,513,some 1024,385979,[OrdSource.row68],.marked⟩
theorem checked292:cell292.check OrdinaryBooks.near 351:=by decide +kernel
def cell293:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,257,some 512,385979,[OrdSource.row66,OrdSource.row67],.marked⟩
theorem checked293:cell293.check OrdinaryBooks.near 351:=by decide +kernel
def cell294:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,161,some 256,385979,[OrdSource.row65],.marked⟩
theorem checked294:cell294.check OrdinaryBooks.near 351:=by decide +kernel
def cell295:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,97,some 160,385979,[OrdSource.row64],.marked⟩
theorem checked295:cell295.check OrdinaryBooks.near 351:=by decide +kernel
def cell296:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,65,some 96,385979,[OrdSource.row62],.marked⟩
theorem checked296:cell296.check OrdinaryBooks.near 351:=by decide +kernel
def cell297:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,48,some 64,385979,[OrdSource.row60],.marked⟩
theorem checked297:cell297.check OrdinaryBooks.near 351:=by decide +kernel
def cell298:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,36,some 47,385979,[OrdSource.row58],.marked⟩
theorem checked298:cell298.check OrdinaryBooks.near 351:=by decide +kernel
def cell299:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,27,some 35,385979,[OrdSource.row56],.marked⟩
theorem checked299:cell299.check OrdinaryBooks.near 351:=by decide +kernel
def cell300:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,21,some 26,385979,[OrdSource.row54],.marked⟩
theorem checked300:cell300.check OrdinaryBooks.near 351:=by decide +kernel
def cell301:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,18,some 20,385979,[OrdSource.row53],.surface⟩
theorem checked301:cell301.check OrdinaryBooks.near 351:=by decide +kernel
def cell302:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,17,some 17,385979,[OrdSource.row52],.surface⟩
theorem checked302:cell302.check OrdinaryBooks.near 351:=by decide +kernel
def cell303:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,15,some 16,385979,[OrdSource.row51],.surface⟩
theorem checked303:cell303.check OrdinaryBooks.near 351:=by decide +kernel
def cell304:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,10,some 14,385979,[],.surface⟩
theorem checked304:cell304.check OrdinaryBooks.near 351:=by decide +kernel
def cell305:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,6,some 9,385979,[],.surface⟩
theorem checked305:cell305.check OrdinaryBooks.near 351:=by decide +kernel
def cell306:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,3,some 5,385979,[],.surface⟩
theorem checked306:cell306.check OrdinaryBooks.near 351:=by decide +kernel
def cell307:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,1,some 2,385979,[],.surface⟩
theorem checked307:cell307.check OrdinaryBooks.near 351:=by decide +kernel
def cell308:OrdinaryCell.Row 2314 2411:=⟨25,27,9,3,0,some 0,385979,[],.ambient⟩
theorem checked308:cell308.check OrdinaryBooks.near 351:=by decide +kernel
def cell309:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,32769,none,514639,[OrdSource.row100],.excluded⟩
theorem checked309:cell309.check OrdinaryBooks.near 351:=by decide +kernel
def cell310:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,16385,some 32768,514639,[OrdSource.row99],.excluded⟩
theorem checked310:cell310.check OrdinaryBooks.near 351:=by decide +kernel
def cell311:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,8193,some 16384,514639,[OrdSource.row98],.excluded⟩
theorem checked311:cell311.check OrdinaryBooks.near 351:=by decide +kernel
def cell312:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,4097,some 8192,514639,[OrdSource.row97],.excluded⟩
theorem checked312:cell312.check OrdinaryBooks.near 351:=by decide +kernel
def cell313:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,2049,some 4096,514639,[OrdSource.row96],.excluded⟩
theorem checked313:cell313.check OrdinaryBooks.near 351:=by decide +kernel
def cell314:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,1025,some 2048,514639,[OrdSource.row94,OrdSource.row95],.marked⟩
theorem checked314:cell314.check OrdinaryBooks.near 351:=by decide +kernel
def cell315:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,513,some 1024,514639,[OrdSource.row92,OrdSource.row93],.marked⟩
theorem checked315:cell315.check OrdinaryBooks.near 351:=by decide +kernel
def cell316:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,257,some 512,514639,[OrdSource.row91],.marked⟩
theorem checked316:cell316.check OrdinaryBooks.near 351:=by decide +kernel
def cell317:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,161,some 256,514639,[OrdSource.row89],.marked⟩
theorem checked317:cell317.check OrdinaryBooks.near 351:=by decide +kernel
def cell318:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,97,some 160,514639,[OrdSource.row87],.marked⟩
theorem checked318:cell318.check OrdinaryBooks.near 351:=by decide +kernel
def cell319:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,65,some 96,514639,[OrdSource.row85],.marked⟩
theorem checked319:cell319.check OrdinaryBooks.near 351:=by decide +kernel
def cell320:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,48,some 64,514639,[OrdSource.row84],.marked⟩
theorem checked320:cell320.check OrdinaryBooks.near 351:=by decide +kernel
def cell321:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,36,some 47,514639,[OrdSource.row83],.marked⟩
theorem checked321:cell321.check OrdinaryBooks.near 351:=by decide +kernel
def cell322:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,27,some 35,514639,[OrdSource.row82],.marked⟩
theorem checked322:cell322.check OrdinaryBooks.near 351:=by decide +kernel
def cell323:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,21,some 26,514639,[OrdSource.row81],.marked⟩
theorem checked323:cell323.check OrdinaryBooks.near 351:=by decide +kernel
def cell324:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,15,some 20,514639,[OrdSource.row80],.marked⟩
theorem checked324:cell324.check OrdinaryBooks.near 351:=by decide +kernel
def cell325:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,10,some 14,514639,[OrdSource.row79],.surface⟩
theorem checked325:cell325.check OrdinaryBooks.near 351:=by decide +kernel
def cell326:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,6,some 9,514639,[OrdSource.row78],.surface⟩
theorem checked326:cell326.check OrdinaryBooks.near 351:=by decide +kernel
def cell327:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,3,some 5,514639,[OrdSource.row77],.surface⟩
theorem checked327:cell327.check OrdinaryBooks.near 351:=by decide +kernel
def cell328:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,1,some 2,514639,[OrdSource.row76],.surface⟩
theorem checked328:cell328.check OrdinaryBooks.near 351:=by decide +kernel
def cell329:OrdinaryCell.Row 2314 2411:=⟨25,27,9,4,0,some 0,514639,[],.ambient⟩
theorem checked329:cell329.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0931

-- Source: Research6969.OrdChecks006
section Z6969Source0932
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell330:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,32769,none,643299,[OrdSource.row120],.excluded⟩
theorem checked330:cell330.check OrdinaryBooks.near 351:=by decide +kernel
def cell331:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,16385,some 32768,643299,[OrdSource.row119],.excluded⟩
theorem checked331:cell331.check OrdinaryBooks.near 351:=by decide +kernel
def cell332:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,8193,some 16384,643299,[OrdSource.row118],.excluded⟩
theorem checked332:cell332.check OrdinaryBooks.near 351:=by decide +kernel
def cell333:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,4097,some 8192,643299,[OrdSource.row117],.marked⟩
theorem checked333:cell333.check OrdinaryBooks.near 351:=by decide +kernel
def cell334:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,513,some 1024,643299,[OrdSource.row114,OrdSource.row115],.marked⟩
theorem checked334:cell334.check OrdinaryBooks.near 351:=by decide +kernel
def cell335:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,257,some 512,643299,[OrdSource.row113],.marked⟩
theorem checked335:cell335.check OrdinaryBooks.near 351:=by decide +kernel
def cell336:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,161,some 256,643299,[OrdSource.row112],.marked⟩
theorem checked336:cell336.check OrdinaryBooks.near 351:=by decide +kernel
def cell337:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,97,some 160,643299,[OrdSource.row111],.marked⟩
theorem checked337:cell337.check OrdinaryBooks.near 351:=by decide +kernel
def cell338:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,65,some 96,643299,[OrdSource.row110],.marked⟩
theorem checked338:cell338.check OrdinaryBooks.near 351:=by decide +kernel
def cell339:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,48,some 64,643299,[OrdSource.row109],.marked⟩
theorem checked339:cell339.check OrdinaryBooks.near 351:=by decide +kernel
def cell340:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,36,some 47,643299,[OrdSource.row108],.marked⟩
theorem checked340:cell340.check OrdinaryBooks.near 351:=by decide +kernel
def cell341:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,27,some 35,643299,[OrdSource.row107],.marked⟩
theorem checked341:cell341.check OrdinaryBooks.near 351:=by decide +kernel
def cell342:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,21,some 26,643299,[OrdSource.row106],.marked⟩
theorem checked342:cell342.check OrdinaryBooks.near 351:=by decide +kernel
def cell343:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,15,some 20,643299,[OrdSource.row105],.marked⟩
theorem checked343:cell343.check OrdinaryBooks.near 351:=by decide +kernel
def cell344:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,10,some 14,643299,[OrdSource.row104],.marked⟩
theorem checked344:cell344.check OrdinaryBooks.near 351:=by decide +kernel
def cell345:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,6,some 9,643299,[OrdSource.row103],.surface⟩
theorem checked345:cell345.check OrdinaryBooks.near 351:=by decide +kernel
def cell346:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,3,some 5,643299,[OrdSource.row102],.surface⟩
theorem checked346:cell346.check OrdinaryBooks.near 351:=by decide +kernel
def cell347:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,1,some 2,643299,[OrdSource.row101],.surface⟩
theorem checked347:cell347.check OrdinaryBooks.near 351:=by decide +kernel
def cell348:OrdinaryCell.Row 2314 2411:=⟨25,27,9,5,0,some 0,643299,[],.ambient⟩
theorem checked348:cell348.check OrdinaryBooks.near 351:=by decide +kernel
def cell349:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,32769,none,128659,[OrdSource.row14],.excluded⟩
theorem checked349:cell349.check OrdinaryBooks.near 351:=by decide +kernel
def cell350:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,16385,some 32768,128659,[OrdSource.row13],.excluded⟩
theorem checked350:cell350.check OrdinaryBooks.near 351:=by decide +kernel
def cell351:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,8193,some 16384,128659,[OrdSource.row12],.excluded⟩
theorem checked351:cell351.check OrdinaryBooks.near 351:=by decide +kernel
def cell352:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,4097,some 8192,128659,[OrdSource.row11],.excluded⟩
theorem checked352:cell352.check OrdinaryBooks.near 351:=by decide +kernel
def cell353:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,2049,some 4096,128659,[OrdSource.row10],.excluded⟩
theorem checked353:cell353.check OrdinaryBooks.near 351:=by decide +kernel
def cell354:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,1025,some 2048,128659,[OrdSource.row9],.excluded⟩
theorem checked354:cell354.check OrdinaryBooks.near 351:=by decide +kernel
def cell355:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,513,some 1024,128659,[OrdSource.row7,OrdSource.row8],.excluded⟩
theorem checked355:cell355.check OrdinaryBooks.near 351:=by decide +kernel
def cell356:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,257,some 512,128659,[OrdSource.row6],.excluded⟩
theorem checked356:cell356.check OrdinaryBooks.near 351:=by decide +kernel
def cell357:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,161,some 256,128659,[OrdSource.row5],.excluded⟩
theorem checked357:cell357.check OrdinaryBooks.near 351:=by decide +kernel
def cell358:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,97,some 160,128659,[OrdSource.row4],.marked⟩
theorem checked358:cell358.check OrdinaryBooks.near 351:=by decide +kernel
def cell359:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,65,some 96,128659,[OrdSource.row3],.affine⟩
theorem checked359:cell359.check OrdinaryBooks.near 351:=by decide +kernel
def cell360:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,48,some 64,128659,[OrdSource.row2],.affine⟩
theorem checked360:cell360.check OrdinaryBooks.near 351:=by decide +kernel
def cell361:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,36,some 47,128659,[OrdSource.row0],.affine⟩
theorem checked361:cell361.check OrdinaryBooks.near 351:=by decide +kernel
def cell362:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,27,some 35,128659,[],.affine⟩
theorem checked362:cell362.check OrdinaryBooks.near 351:=by decide +kernel
def cell363:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,21,some 26,128659,[],.affine⟩
theorem checked363:cell363.check OrdinaryBooks.near 351:=by decide +kernel
def cell364:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,15,some 20,128659,[],.affine⟩
theorem checked364:cell364.check OrdinaryBooks.near 351:=by decide +kernel
def cell365:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,10,some 14,128659,[],.affine⟩
theorem checked365:cell365.check OrdinaryBooks.near 351:=by decide +kernel
def cell366:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,6,some 9,128659,[],.affine⟩
theorem checked366:cell366.check OrdinaryBooks.near 351:=by decide +kernel
def cell367:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,3,some 5,128659,[],.affine⟩
theorem checked367:cell367.check OrdinaryBooks.near 351:=by decide +kernel
def cell368:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,1,some 2,128659,[],.affine⟩
theorem checked368:cell368.check OrdinaryBooks.near 351:=by decide +kernel
def cell369:OrdinaryCell.Row 2314 2411:=⟨28,32,9,1,0,some 0,128659,[],.affine⟩
theorem checked369:cell369.check OrdinaryBooks.near 351:=by decide +kernel
def cell370:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,32769,none,257319,[OrdSource.row46],.excluded⟩
theorem checked370:cell370.check OrdinaryBooks.near 351:=by decide +kernel
def cell371:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,16385,some 32768,257319,[OrdSource.row45],.excluded⟩
theorem checked371:cell371.check OrdinaryBooks.near 351:=by decide +kernel
def cell372:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,8193,some 16384,257319,[OrdSource.row44],.excluded⟩
theorem checked372:cell372.check OrdinaryBooks.near 351:=by decide +kernel
def cell373:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,4097,some 8192,257319,[OrdSource.row43],.excluded⟩
theorem checked373:cell373.check OrdinaryBooks.near 351:=by decide +kernel
def cell374:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,2049,some 4096,257319,[OrdSource.row42],.excluded⟩
theorem checked374:cell374.check OrdinaryBooks.near 351:=by decide +kernel
def cell375:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,1025,some 2048,257319,[OrdSource.row40,OrdSource.row41],.excluded⟩
theorem checked375:cell375.check OrdinaryBooks.near 351:=by decide +kernel
def cell376:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,513,some 1024,257319,[OrdSource.row39],.excluded⟩
theorem checked376:cell376.check OrdinaryBooks.near 351:=by decide +kernel
def cell377:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,257,some 512,257319,[OrdSource.row37,OrdSource.row38],.excluded⟩
theorem checked377:cell377.check OrdinaryBooks.near 351:=by decide +kernel
def cell378:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,161,some 256,257319,[OrdSource.row36],.marked⟩
theorem checked378:cell378.check OrdinaryBooks.near 351:=by decide +kernel
def cell379:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,97,some 160,257319,[OrdSource.row32,OrdSource.row33],.marked⟩
theorem checked379:cell379.check OrdinaryBooks.near 351:=by decide +kernel
def cell380:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,65,some 96,257319,[OrdSource.row30],.marked⟩
theorem checked380:cell380.check OrdinaryBooks.near 351:=by decide +kernel
def cell381:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,48,some 64,257319,[OrdSource.row23],.marked⟩
theorem checked381:cell381.check OrdinaryBooks.near 351:=by decide +kernel
def cell382:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,36,some 47,257319,[OrdSource.row19],.marked⟩
theorem checked382:cell382.check OrdinaryBooks.near 351:=by decide +kernel
def cell383:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,27,some 35,257319,[OrdSource.row15],(.node 8043223611471520 299354)⟩
theorem checked383:cell383.check OrdinaryBooks.near 351:=by decide +kernel
def cell384:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,27,some 35,299354,[OrdSource.row47],.surface⟩
theorem checked384:cell384.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0932

-- Source: Research6969.OrdRouteNear2
section Z6969Source0933
set_option autoImplicit true
namespace Research6969.OrdRouteNear2
open OrdinaryRoute
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000
private theorem leaf258:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,32769,none⟩:=
  plain OrdReceipts.cell243 OrdReceipts.checked243 (by decide) (by decide)
private theorem leaf259:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,16385,some 32768⟩:=
  plain OrdReceipts.cell244 OrdReceipts.checked244 (by decide) (by decide)
private theorem leaf260:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,8193,some 16384⟩:=
  plain OrdReceipts.cell245 OrdReceipts.checked245 (by decide) (by decide)
private theorem leaf261:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,4097,some 8192⟩:=
  plain OrdReceipts.cell246 OrdReceipts.checked246 (by decide) (by decide)
private theorem leaf262:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,2049,some 4096⟩:=
  plain OrdReceipts.cell247 OrdReceipts.checked247 (by decide) (by decide)
private theorem leaf263:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,1025,some 2048⟩:=
  plain OrdReceipts.cell248 OrdReceipts.checked248 (by decide) (by decide)
private theorem leaf264:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,513,some 1024⟩:=
  plain OrdReceipts.cell249 OrdReceipts.checked249 (by decide) (by decide)
private theorem leaf265:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,257,some 512⟩:=
  plain OrdReceipts.cell250 OrdReceipts.checked250 (by decide) (by decide)
private theorem leaf266:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,161,some 256⟩:=
  plain OrdReceipts.cell251 OrdReceipts.checked251 (by decide) (by decide)
private theorem leaf267:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,97,some 160⟩:=
  plain OrdReceipts.cell252 OrdReceipts.checked252 (by decide) (by decide)
private theorem leaf268:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,65,some 96⟩:=
  plain OrdReceipts.cell253 OrdReceipts.checked253 (by decide) (by decide)
private theorem leaf269:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,48,some 64⟩:=
  plain OrdReceipts.cell254 OrdReceipts.checked254 (by decide) (by decide)
private theorem leaf270:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,36,some 47⟩:=
  plain OrdReceipts.cell255 OrdReceipts.checked255 (by decide) (by decide)
private theorem leaf271:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,27,some 35⟩:=
  plain OrdReceipts.cell256 OrdReceipts.checked256 (by decide) (by decide)
private theorem leaf272:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,21,some 26⟩:=
  plain OrdReceipts.cell257 OrdReceipts.checked257 (by decide) (by decide)
private theorem leaf273:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,15,some 20⟩:=
  plain OrdReceipts.cell258 OrdReceipts.checked258 (by decide) (by decide)
private theorem leaf274:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,10,some 14⟩:=
  plain OrdReceipts.cell259 OrdReceipts.checked259 (by decide) (by decide)
private theorem leaf275:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,6,some 9⟩:=
  plain OrdReceipts.cell260 OrdReceipts.checked260 (by decide) (by decide)
private theorem leaf276:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,3,some 5⟩:=
  plain OrdReceipts.cell261 OrdReceipts.checked261 (by decide) (by decide)
private theorem leaf277:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,1,some 2⟩:=
  plain OrdReceipts.cell262 OrdReceipts.checked262 (by decide) (by decide)
private theorem leaf278:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,1,0,some 0⟩:=
  plain OrdReceipts.cell263 OrdReceipts.checked263 (by decide) (by decide)
private theorem leaf279:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,32769,none⟩:=
  plain OrdReceipts.cell264 OrdReceipts.checked264 (by decide) (by decide)
private theorem leaf280:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,16385,some 32768⟩:=
  plain OrdReceipts.cell265 OrdReceipts.checked265 (by decide) (by decide)
private theorem leaf281:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,8193,some 16384⟩:=
  plain OrdReceipts.cell266 OrdReceipts.checked266 (by decide) (by decide)
private theorem leaf282:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,4097,some 8192⟩:=
  plain OrdReceipts.cell267 OrdReceipts.checked267 (by decide) (by decide)
private theorem leaf283:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,2049,some 4096⟩:=
  plain OrdReceipts.cell268 OrdReceipts.checked268 (by decide) (by decide)
private theorem leaf284:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,1025,some 2048⟩:=
  plain OrdReceipts.cell269 OrdReceipts.checked269 (by decide) (by decide)
private theorem leaf285:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,513,some 1024⟩:=
  plain OrdReceipts.cell270 OrdReceipts.checked270 (by decide) (by decide)
private theorem leaf286:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,257,some 512⟩:=
  plain OrdReceipts.cell271 OrdReceipts.checked271 (by decide) (by decide)
private theorem leaf287:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,161,some 256⟩:=
  plain OrdReceipts.cell272 OrdReceipts.checked272 (by decide) (by decide)
private theorem leaf288:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,97,some 160⟩:=
  plain OrdReceipts.cell273 OrdReceipts.checked273 (by decide) (by decide)
private theorem leaf289:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,65,some 96⟩:=
  plain OrdReceipts.cell274 OrdReceipts.checked274 (by decide) (by decide)
private theorem leaf290:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,48,some 64⟩:=
  plain OrdReceipts.cell275 OrdReceipts.checked275 (by decide) (by decide)
private theorem leaf291:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,36,some 47⟩:=
  plain OrdReceipts.cell276 OrdReceipts.checked276 (by decide) (by decide)
private theorem leaf292:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,27,some 35⟩:=
  physical OrdReceipts.cell277 OrdReceipts.cell278 OrdReceipts.checked277 OrdReceipts.checked278 rfl 299354 (by decide) (by decide) (by decide) (by decide)
private theorem leaf293:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,21,some 26⟩:=
  plain OrdReceipts.cell279 OrdReceipts.checked279 (by decide) (by decide)
private theorem leaf294:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,15,some 20⟩:=
  plain OrdReceipts.cell280 OrdReceipts.checked280 (by decide) (by decide)
private theorem leaf295:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,10,some 14⟩:=
  plain OrdReceipts.cell281 OrdReceipts.checked281 (by decide) (by decide)
private theorem leaf296:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,6,some 9⟩:=
  plain OrdReceipts.cell282 OrdReceipts.checked282 (by decide) (by decide)
private theorem leaf297:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,3,some 5⟩:=
  plain OrdReceipts.cell283 OrdReceipts.checked283 (by decide) (by decide)
private theorem leaf298:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,1,some 2⟩:=
  plain OrdReceipts.cell284 OrdReceipts.checked284 (by decide) (by decide)
private theorem leaf299:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,2,0,some 0⟩:=
  plain OrdReceipts.cell285 OrdReceipts.checked285 (by decide) (by decide)
private theorem leaf300:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,32769,none⟩:=
  plain OrdReceipts.cell286 OrdReceipts.checked286 (by decide) (by decide)
private theorem leaf301:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,16385,some 32768⟩:=
  plain OrdReceipts.cell287 OrdReceipts.checked287 (by decide) (by decide)
private theorem leaf302:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,8193,some 16384⟩:=
  plain OrdReceipts.cell288 OrdReceipts.checked288 (by decide) (by decide)
private theorem leaf303:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,4097,some 8192⟩:=
  plain OrdReceipts.cell289 OrdReceipts.checked289 (by decide) (by decide)
private theorem leaf304:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,2049,some 4096⟩:=
  plain OrdReceipts.cell290 OrdReceipts.checked290 (by decide) (by decide)
private theorem leaf305:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,1025,some 2048⟩:=
  plain OrdReceipts.cell291 OrdReceipts.checked291 (by decide) (by decide)
private theorem leaf306:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,513,some 1024⟩:=
  plain OrdReceipts.cell292 OrdReceipts.checked292 (by decide) (by decide)
private theorem leaf307:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,257,some 512⟩:=
  plain OrdReceipts.cell293 OrdReceipts.checked293 (by decide) (by decide)
private theorem leaf308:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,161,some 256⟩:=
  plain OrdReceipts.cell294 OrdReceipts.checked294 (by decide) (by decide)
private theorem leaf309:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,97,some 160⟩:=
  plain OrdReceipts.cell295 OrdReceipts.checked295 (by decide) (by decide)
private theorem leaf310:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,65,some 96⟩:=
  plain OrdReceipts.cell296 OrdReceipts.checked296 (by decide) (by decide)
private theorem leaf311:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,48,some 64⟩:=
  plain OrdReceipts.cell297 OrdReceipts.checked297 (by decide) (by decide)
private theorem leaf312:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,36,some 47⟩:=
  plain OrdReceipts.cell298 OrdReceipts.checked298 (by decide) (by decide)
private theorem leaf313:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,27,some 35⟩:=
  plain OrdReceipts.cell299 OrdReceipts.checked299 (by decide) (by decide)
private theorem leaf314:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,21,some 26⟩:=
  plain OrdReceipts.cell300 OrdReceipts.checked300 (by decide) (by decide)
private theorem leaf315:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,18,some 20⟩:=
  plain OrdReceipts.cell301 OrdReceipts.checked301 (by decide) (by decide)
private theorem leaf316:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,17,some 17⟩:=
  plain OrdReceipts.cell302 OrdReceipts.checked302 (by decide) (by decide)
private theorem leaf317:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,15,some 16⟩:=
  plain OrdReceipts.cell303 OrdReceipts.checked303 (by decide) (by decide)
private theorem leaf318:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,10,some 14⟩:=
  plain OrdReceipts.cell304 OrdReceipts.checked304 (by decide) (by decide)
private theorem leaf319:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,6,some 9⟩:=
  plain OrdReceipts.cell305 OrdReceipts.checked305 (by decide) (by decide)
private theorem leaf320:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,3,some 5⟩:=
  plain OrdReceipts.cell306 OrdReceipts.checked306 (by decide) (by decide)
private theorem leaf321:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,1,some 2⟩:=
  plain OrdReceipts.cell307 OrdReceipts.checked307 (by decide) (by decide)
private theorem leaf322:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,3,0,some 0⟩:=
  plain OrdReceipts.cell308 OrdReceipts.checked308 (by decide) (by decide)
private theorem leaf323:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,32769,none⟩:=
  plain OrdReceipts.cell309 OrdReceipts.checked309 (by decide) (by decide)
private theorem leaf324:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,16385,some 32768⟩:=
  plain OrdReceipts.cell310 OrdReceipts.checked310 (by decide) (by decide)
private theorem leaf325:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,8193,some 16384⟩:=
  plain OrdReceipts.cell311 OrdReceipts.checked311 (by decide) (by decide)
private theorem leaf326:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,4097,some 8192⟩:=
  plain OrdReceipts.cell312 OrdReceipts.checked312 (by decide) (by decide)
private theorem leaf327:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,2049,some 4096⟩:=
  plain OrdReceipts.cell313 OrdReceipts.checked313 (by decide) (by decide)
private theorem leaf328:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,1025,some 2048⟩:=
  plain OrdReceipts.cell314 OrdReceipts.checked314 (by decide) (by decide)
private theorem leaf329:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,513,some 1024⟩:=
  plain OrdReceipts.cell315 OrdReceipts.checked315 (by decide) (by decide)
private theorem leaf330:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,257,some 512⟩:=
  plain OrdReceipts.cell316 OrdReceipts.checked316 (by decide) (by decide)
private theorem leaf331:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,161,some 256⟩:=
  plain OrdReceipts.cell317 OrdReceipts.checked317 (by decide) (by decide)
private theorem leaf332:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,97,some 160⟩:=
  plain OrdReceipts.cell318 OrdReceipts.checked318 (by decide) (by decide)
private theorem leaf333:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,65,some 96⟩:=
  plain OrdReceipts.cell319 OrdReceipts.checked319 (by decide) (by decide)
private theorem leaf334:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,48,some 64⟩:=
  plain OrdReceipts.cell320 OrdReceipts.checked320 (by decide) (by decide)
private theorem leaf335:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,36,some 47⟩:=
  plain OrdReceipts.cell321 OrdReceipts.checked321 (by decide) (by decide)
private theorem leaf336:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,27,some 35⟩:=
  plain OrdReceipts.cell322 OrdReceipts.checked322 (by decide) (by decide)
private theorem leaf337:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,21,some 26⟩:=
  plain OrdReceipts.cell323 OrdReceipts.checked323 (by decide) (by decide)
private theorem leaf338:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,15,some 20⟩:=
  plain OrdReceipts.cell324 OrdReceipts.checked324 (by decide) (by decide)
private theorem leaf339:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,10,some 14⟩:=
  plain OrdReceipts.cell325 OrdReceipts.checked325 (by decide) (by decide)
private theorem leaf340:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,6,some 9⟩:=
  plain OrdReceipts.cell326 OrdReceipts.checked326 (by decide) (by decide)
private theorem leaf341:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,3,some 5⟩:=
  plain OrdReceipts.cell327 OrdReceipts.checked327 (by decide) (by decide)
private theorem leaf342:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,1,some 2⟩:=
  plain OrdReceipts.cell328 OrdReceipts.checked328 (by decide) (by decide)
private theorem leaf343:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,4,0,some 0⟩:=
  plain OrdReceipts.cell329 OrdReceipts.checked329 (by decide) (by decide)
private theorem leaf344:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,32769,none⟩:=
  plain OrdReceipts.cell330 OrdReceipts.checked330 (by decide) (by decide)
private theorem leaf345:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,16385,some 32768⟩:=
  plain OrdReceipts.cell331 OrdReceipts.checked331 (by decide) (by decide)
private theorem leaf346:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,8193,some 16384⟩:=
  plain OrdReceipts.cell332 OrdReceipts.checked332 (by decide) (by decide)
private theorem leaf347:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,4097,some 8192⟩:=
  plain OrdReceipts.cell333 OrdReceipts.checked333 (by decide) (by decide)
private theorem leaf348:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,2049,some 4096⟩:=
  power _ 643299 (by decide) OrdPower.covered17 (by decide) (by decide) (by decide)
private theorem leaf349:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,1025,some 2048⟩:=
  power _ 643299 (by decide) OrdPower.covered16 (by decide) (by decide) (by decide)
private theorem leaf350:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,513,some 1024⟩:=
  plain OrdReceipts.cell334 OrdReceipts.checked334 (by decide) (by decide)
private theorem leaf351:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,257,some 512⟩:=
  plain OrdReceipts.cell335 OrdReceipts.checked335 (by decide) (by decide)
private theorem leaf352:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,161,some 256⟩:=
  plain OrdReceipts.cell336 OrdReceipts.checked336 (by decide) (by decide)
private theorem leaf353:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,97,some 160⟩:=
  plain OrdReceipts.cell337 OrdReceipts.checked337 (by decide) (by decide)
private theorem leaf354:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,65,some 96⟩:=
  plain OrdReceipts.cell338 OrdReceipts.checked338 (by decide) (by decide)
private theorem leaf355:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,48,some 64⟩:=
  plain OrdReceipts.cell339 OrdReceipts.checked339 (by decide) (by decide)
private theorem leaf356:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,36,some 47⟩:=
  plain OrdReceipts.cell340 OrdReceipts.checked340 (by decide) (by decide)
private theorem leaf357:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,27,some 35⟩:=
  plain OrdReceipts.cell341 OrdReceipts.checked341 (by decide) (by decide)
private theorem leaf358:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,21,some 26⟩:=
  plain OrdReceipts.cell342 OrdReceipts.checked342 (by decide) (by decide)
private theorem leaf359:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,15,some 20⟩:=
  plain OrdReceipts.cell343 OrdReceipts.checked343 (by decide) (by decide)
private theorem leaf360:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,10,some 14⟩:=
  plain OrdReceipts.cell344 OrdReceipts.checked344 (by decide) (by decide)
private theorem leaf361:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,6,some 9⟩:=
  plain OrdReceipts.cell345 OrdReceipts.checked345 (by decide) (by decide)
private theorem leaf362:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,3,some 5⟩:=
  plain OrdReceipts.cell346 OrdReceipts.checked346 (by decide) (by decide)
private theorem leaf363:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,1,some 2⟩:=
  plain OrdReceipts.cell347 OrdReceipts.checked347 (by decide) (by decide)
private theorem leaf364:Done 2314 2411 OrdinaryBooks.near 351 ⟨25,27,9,5,0,some 0⟩:=
  plain OrdReceipts.cell348 OrdReceipts.checked348 (by decide) (by decide)
private theorem tail1_32769:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 32769:=leaf258
private theorem tail1_16385:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 16385:=join leaf259 tail1_32769
private theorem tail1_8193:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 8193:=join leaf260 tail1_16385
private theorem tail1_4097:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 4097:=join leaf261 tail1_8193
private theorem tail1_2049:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 2049:=join leaf262 tail1_4097
private theorem tail1_1025:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 1025:=join leaf263 tail1_2049
private theorem tail1_513:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 513:=join leaf264 tail1_1025
private theorem tail1_257:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 257:=join leaf265 tail1_513
private theorem tail1_161:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 161:=join leaf266 tail1_257
private theorem tail1_97:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 97:=join leaf267 tail1_161
private theorem tail1_65:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 65:=join leaf268 tail1_97
private theorem tail1_48:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 48:=join leaf269 tail1_65
private theorem tail1_36:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 36:=join leaf270 tail1_48
private theorem tail1_27:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 27:=join leaf271 tail1_36
private theorem tail1_21:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 21:=join leaf272 tail1_27
private theorem tail1_15:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 15:=join leaf273 tail1_21
private theorem tail1_10:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 10:=join leaf274 tail1_15
private theorem tail1_6:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 6:=join leaf275 tail1_10
private theorem tail1_3:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 3:=join leaf276 tail1_6
private theorem tail1_1:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 1:=join leaf277 tail1_3
private theorem tail1_0:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 1 0:=join leaf278 tail1_1
private theorem tail2_32769:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 32769:=leaf279
private theorem tail2_16385:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 16385:=join leaf280 tail2_32769
private theorem tail2_8193:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 8193:=join leaf281 tail2_16385
private theorem tail2_4097:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 4097:=join leaf282 tail2_8193
private theorem tail2_2049:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 2049:=join leaf283 tail2_4097
private theorem tail2_1025:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 1025:=join leaf284 tail2_2049
private theorem tail2_513:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 513:=join leaf285 tail2_1025
private theorem tail2_257:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 257:=join leaf286 tail2_513
private theorem tail2_161:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 161:=join leaf287 tail2_257
private theorem tail2_97:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 97:=join leaf288 tail2_161
private theorem tail2_65:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 65:=join leaf289 tail2_97
private theorem tail2_48:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 48:=join leaf290 tail2_65
private theorem tail2_36:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 36:=join leaf291 tail2_48
private theorem tail2_27:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 27:=join leaf292 tail2_36
private theorem tail2_21:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 21:=join leaf293 tail2_27
private theorem tail2_15:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 15:=join leaf294 tail2_21
private theorem tail2_10:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 10:=join leaf295 tail2_15
private theorem tail2_6:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 6:=join leaf296 tail2_10
private theorem tail2_3:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 3:=join leaf297 tail2_6
private theorem tail2_1:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 1:=join leaf298 tail2_3
private theorem tail2_0:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 2 0:=join leaf299 tail2_1
private theorem tail3_32769:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 32769:=leaf300
private theorem tail3_16385:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 16385:=join leaf301 tail3_32769
private theorem tail3_8193:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 8193:=join leaf302 tail3_16385
private theorem tail3_4097:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 4097:=join leaf303 tail3_8193
private theorem tail3_2049:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 2049:=join leaf304 tail3_4097
private theorem tail3_1025:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 1025:=join leaf305 tail3_2049
private theorem tail3_513:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 513:=join leaf306 tail3_1025
private theorem tail3_257:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 257:=join leaf307 tail3_513
private theorem tail3_161:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 161:=join leaf308 tail3_257
private theorem tail3_97:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 97:=join leaf309 tail3_161
private theorem tail3_65:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 65:=join leaf310 tail3_97
private theorem tail3_48:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 48:=join leaf311 tail3_65
private theorem tail3_36:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 36:=join leaf312 tail3_48
private theorem tail3_27:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 27:=join leaf313 tail3_36
private theorem tail3_21:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 21:=join leaf314 tail3_27
private theorem tail3_18:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 18:=join leaf315 tail3_21
private theorem tail3_17:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 17:=join leaf316 tail3_18
private theorem tail3_15:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 15:=join leaf317 tail3_17
private theorem tail3_10:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 10:=join leaf318 tail3_15
private theorem tail3_6:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 6:=join leaf319 tail3_10
private theorem tail3_3:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 3:=join leaf320 tail3_6
private theorem tail3_1:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 1:=join leaf321 tail3_3
private theorem tail3_0:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 3 0:=join leaf322 tail3_1
private theorem tail4_32769:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 32769:=leaf323
private theorem tail4_16385:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 16385:=join leaf324 tail4_32769
private theorem tail4_8193:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 8193:=join leaf325 tail4_16385
private theorem tail4_4097:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 4097:=join leaf326 tail4_8193
private theorem tail4_2049:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 2049:=join leaf327 tail4_4097
private theorem tail4_1025:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 1025:=join leaf328 tail4_2049
private theorem tail4_513:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 513:=join leaf329 tail4_1025
private theorem tail4_257:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 257:=join leaf330 tail4_513
private theorem tail4_161:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 161:=join leaf331 tail4_257
private theorem tail4_97:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 97:=join leaf332 tail4_161
private theorem tail4_65:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 65:=join leaf333 tail4_97
private theorem tail4_48:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 48:=join leaf334 tail4_65
private theorem tail4_36:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 36:=join leaf335 tail4_48
private theorem tail4_27:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 27:=join leaf336 tail4_36
private theorem tail4_21:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 21:=join leaf337 tail4_27
private theorem tail4_15:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 15:=join leaf338 tail4_21
private theorem tail4_10:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 10:=join leaf339 tail4_15
private theorem tail4_6:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 6:=join leaf340 tail4_10
private theorem tail4_3:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 3:=join leaf341 tail4_6
private theorem tail4_1:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 1:=join leaf342 tail4_3
private theorem tail4_0:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 4 0:=join leaf343 tail4_1
private theorem tail5_32769:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 32769:=leaf344
private theorem tail5_16385:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 16385:=join leaf345 tail5_32769
private theorem tail5_8193:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 8193:=join leaf346 tail5_16385
private theorem tail5_4097:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 4097:=join leaf347 tail5_8193
private theorem tail5_2049:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 2049:=join leaf348 tail5_4097
private theorem tail5_1025:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 1025:=join leaf349 tail5_2049
private theorem tail5_513:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 513:=join leaf350 tail5_1025
private theorem tail5_257:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 257:=join leaf351 tail5_513
private theorem tail5_161:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 161:=join leaf352 tail5_257
private theorem tail5_97:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 97:=join leaf353 tail5_161
private theorem tail5_65:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 65:=join leaf354 tail5_97
private theorem tail5_48:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 48:=join leaf355 tail5_65
private theorem tail5_36:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 36:=join leaf356 tail5_48
private theorem tail5_27:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 27:=join leaf357 tail5_36
private theorem tail5_21:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 21:=join leaf358 tail5_27
private theorem tail5_15:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 15:=join leaf359 tail5_21
private theorem tail5_10:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 10:=join leaf360 tail5_15
private theorem tail5_6:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 6:=join leaf361 tail5_10
private theorem tail5_3:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 3:=join leaf362 tail5_6
private theorem tail5_1:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 1:=join leaf363 tail5_3
private theorem tail5_0:Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 5 0:=join leaf364 tail5_1
theorem allDegrees (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail 2314 2411 OrdinaryBooks.near 351 25 27 9 a 0:=by
  interval_cases a
  · exact tail1_0
  · exact tail2_0
  · exact tail3_0
  · exact tail4_0
  · exact tail5_0
end Research6969.OrdRouteNear2
end Z6969Source0933

-- Source: Research6969.OrdChecks007
section Z6969Source0934
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell385:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,21,some 26,257319,[],.surface⟩
theorem checked385:cell385.check OrdinaryBooks.near 351:=by decide +kernel
def cell386:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,15,some 20,257319,[],.surface⟩
theorem checked386:cell386.check OrdinaryBooks.near 351:=by decide +kernel
def cell387:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,10,some 14,257319,[],.surface⟩
theorem checked387:cell387.check OrdinaryBooks.near 351:=by decide +kernel
def cell388:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,6,some 9,257319,[],.surface⟩
theorem checked388:cell388.check OrdinaryBooks.near 351:=by decide +kernel
def cell389:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,3,some 5,257319,[],.surface⟩
theorem checked389:cell389.check OrdinaryBooks.near 351:=by decide +kernel
def cell390:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,1,some 2,257319,[],.surface⟩
theorem checked390:cell390.check OrdinaryBooks.near 351:=by decide +kernel
def cell391:OrdinaryCell.Row 2314 2411:=⟨28,32,9,2,0,some 0,257319,[],.ambient⟩
theorem checked391:cell391.check OrdinaryBooks.near 351:=by decide +kernel
def cell392:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,32769,none,385979,[OrdSource.row75],.excluded⟩
theorem checked392:cell392.check OrdinaryBooks.near 351:=by decide +kernel
def cell393:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,16385,some 32768,385979,[OrdSource.row74],.excluded⟩
theorem checked393:cell393.check OrdinaryBooks.near 351:=by decide +kernel
def cell394:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,8193,some 16384,385979,[OrdSource.row73],.excluded⟩
theorem checked394:cell394.check OrdinaryBooks.near 351:=by decide +kernel
def cell395:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,4097,some 8192,385979,[OrdSource.row72],.excluded⟩
theorem checked395:cell395.check OrdinaryBooks.near 351:=by decide +kernel
def cell396:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,2049,some 4096,385979,[OrdSource.row71],.excluded⟩
theorem checked396:cell396.check OrdinaryBooks.near 351:=by decide +kernel
def cell397:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,1025,some 2048,385979,[OrdSource.row69,OrdSource.row70],.excluded⟩
theorem checked397:cell397.check OrdinaryBooks.near 351:=by decide +kernel
def cell398:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,513,some 1024,385979,[OrdSource.row68],.excluded⟩
theorem checked398:cell398.check OrdinaryBooks.near 351:=by decide +kernel
def cell399:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,257,some 512,385979,[OrdSource.row66,OrdSource.row67],.marked⟩
theorem checked399:cell399.check OrdinaryBooks.near 351:=by decide +kernel
def cell400:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,161,some 256,385979,[OrdSource.row65],.marked⟩
theorem checked400:cell400.check OrdinaryBooks.near 351:=by decide +kernel
def cell401:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,97,some 160,385979,[OrdSource.row64],.marked⟩
theorem checked401:cell401.check OrdinaryBooks.near 351:=by decide +kernel
def cell402:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,65,some 96,385979,[OrdSource.row62],.marked⟩
theorem checked402:cell402.check OrdinaryBooks.near 351:=by decide +kernel
def cell403:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,48,some 64,385979,[OrdSource.row60],.marked⟩
theorem checked403:cell403.check OrdinaryBooks.near 351:=by decide +kernel
def cell404:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,36,some 47,385979,[OrdSource.row58],.marked⟩
theorem checked404:cell404.check OrdinaryBooks.near 351:=by decide +kernel
def cell405:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,27,some 35,385979,[OrdSource.row56],.marked⟩
theorem checked405:cell405.check OrdinaryBooks.near 351:=by decide +kernel
def cell406:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,24,some 26,385979,[OrdSource.row55],.surface⟩
theorem checked406:cell406.check OrdinaryBooks.near 351:=by decide +kernel
def cell407:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,21,some 23,385979,[OrdSource.row54],.surface⟩
theorem checked407:cell407.check OrdinaryBooks.near 351:=by decide +kernel
def cell408:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,18,some 20,385979,[OrdSource.row53],.surface⟩
theorem checked408:cell408.check OrdinaryBooks.near 351:=by decide +kernel
def cell409:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,17,some 17,385979,[OrdSource.row52],.surface⟩
theorem checked409:cell409.check OrdinaryBooks.near 351:=by decide +kernel
def cell410:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,15,some 16,385979,[OrdSource.row51],.surface⟩
theorem checked410:cell410.check OrdinaryBooks.near 351:=by decide +kernel
def cell411:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,10,some 14,385979,[],.surface⟩
theorem checked411:cell411.check OrdinaryBooks.near 351:=by decide +kernel
def cell412:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,6,some 9,385979,[],.surface⟩
theorem checked412:cell412.check OrdinaryBooks.near 351:=by decide +kernel
def cell413:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,3,some 5,385979,[],.surface⟩
theorem checked413:cell413.check OrdinaryBooks.near 351:=by decide +kernel
def cell414:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,1,some 2,385979,[],.surface⟩
theorem checked414:cell414.check OrdinaryBooks.near 351:=by decide +kernel
def cell415:OrdinaryCell.Row 2314 2411:=⟨28,32,9,3,0,some 0,385979,[],.ambient⟩
theorem checked415:cell415.check OrdinaryBooks.near 351:=by decide +kernel
def cell416:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,32769,none,514639,[OrdSource.row100],.excluded⟩
theorem checked416:cell416.check OrdinaryBooks.near 351:=by decide +kernel
def cell417:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,16385,some 32768,514639,[OrdSource.row99],.excluded⟩
theorem checked417:cell417.check OrdinaryBooks.near 351:=by decide +kernel
def cell418:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,8193,some 16384,514639,[OrdSource.row98],.excluded⟩
theorem checked418:cell418.check OrdinaryBooks.near 351:=by decide +kernel
def cell419:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,4097,some 8192,514639,[OrdSource.row97],.excluded⟩
theorem checked419:cell419.check OrdinaryBooks.near 351:=by decide +kernel
def cell420:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,2049,some 4096,514639,[OrdSource.row96],.excluded⟩
theorem checked420:cell420.check OrdinaryBooks.near 351:=by decide +kernel
def cell421:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,1025,some 2048,514639,[OrdSource.row94,OrdSource.row95],.excluded⟩
theorem checked421:cell421.check OrdinaryBooks.near 351:=by decide +kernel
def cell422:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,513,some 1024,514639,[OrdSource.row92,OrdSource.row93],.marked⟩
theorem checked422:cell422.check OrdinaryBooks.near 351:=by decide +kernel
def cell423:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,257,some 512,514639,[OrdSource.row90,OrdSource.row91],.marked⟩
theorem checked423:cell423.check OrdinaryBooks.near 351:=by decide +kernel
def cell424:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,161,some 256,514639,[OrdSource.row88,OrdSource.row89],.marked⟩
theorem checked424:cell424.check OrdinaryBooks.near 351:=by decide +kernel
def cell425:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,97,some 160,514639,[OrdSource.row87],.marked⟩
theorem checked425:cell425.check OrdinaryBooks.near 351:=by decide +kernel
def cell426:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,65,some 96,514639,[OrdSource.row85],.marked⟩
theorem checked426:cell426.check OrdinaryBooks.near 351:=by decide +kernel
def cell427:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,48,some 64,514639,[OrdSource.row84],.marked⟩
theorem checked427:cell427.check OrdinaryBooks.near 351:=by decide +kernel
def cell428:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,36,some 47,514639,[OrdSource.row83],.marked⟩
theorem checked428:cell428.check OrdinaryBooks.near 351:=by decide +kernel
def cell429:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,27,some 35,514639,[OrdSource.row82],.marked⟩
theorem checked429:cell429.check OrdinaryBooks.near 351:=by decide +kernel
def cell430:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,21,some 26,514639,[OrdSource.row81],.marked⟩
theorem checked430:cell430.check OrdinaryBooks.near 351:=by decide +kernel
def cell431:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,15,some 20,514639,[OrdSource.row80],.surface⟩
theorem checked431:cell431.check OrdinaryBooks.near 351:=by decide +kernel
def cell432:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,10,some 14,514639,[OrdSource.row79],.surface⟩
theorem checked432:cell432.check OrdinaryBooks.near 351:=by decide +kernel
def cell433:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,6,some 9,514639,[OrdSource.row78],.surface⟩
theorem checked433:cell433.check OrdinaryBooks.near 351:=by decide +kernel
def cell434:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,3,some 5,514639,[OrdSource.row77],.surface⟩
theorem checked434:cell434.check OrdinaryBooks.near 351:=by decide +kernel
def cell435:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,1,some 2,514639,[OrdSource.row76],.surface⟩
theorem checked435:cell435.check OrdinaryBooks.near 351:=by decide +kernel
def cell436:OrdinaryCell.Row 2314 2411:=⟨28,32,9,4,0,some 0,514639,[],.ambient⟩
theorem checked436:cell436.check OrdinaryBooks.near 351:=by decide +kernel
def cell437:OrdinaryCell.Row 2314 2411:=⟨33,40,9,1,32769,none,128659,[OrdSource.row14],.excluded⟩
theorem checked437:cell437.check OrdinaryBooks.near 351:=by decide +kernel
def cell438:OrdinaryCell.Row 2314 2411:=⟨33,40,9,1,16385,some 32768,128659,[OrdSource.row13],.excluded⟩
theorem checked438:cell438.check OrdinaryBooks.near 351:=by decide +kernel
def cell439:OrdinaryCell.Row 2314 2411:=⟨33,40,9,1,8193,some 16384,128659,[OrdSource.row12],.excluded⟩
theorem checked439:cell439.check OrdinaryBooks.near 351:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source0934

-- Source: Research6969.OrdRouteNear3
section Z6969Source0935
set_option autoImplicit true
namespace Research6969.OrdRouteNear3
open OrdinaryRoute
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000
private theorem leaf365:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,32769,none⟩:=
  plain OrdReceipts.cell349 OrdReceipts.checked349 (by decide) (by decide)
private theorem leaf366:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,16385,some 32768⟩:=
  plain OrdReceipts.cell350 OrdReceipts.checked350 (by decide) (by decide)
private theorem leaf367:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,8193,some 16384⟩:=
  plain OrdReceipts.cell351 OrdReceipts.checked351 (by decide) (by decide)
private theorem leaf368:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,4097,some 8192⟩:=
  plain OrdReceipts.cell352 OrdReceipts.checked352 (by decide) (by decide)
private theorem leaf369:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,2049,some 4096⟩:=
  plain OrdReceipts.cell353 OrdReceipts.checked353 (by decide) (by decide)
private theorem leaf370:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,1025,some 2048⟩:=
  plain OrdReceipts.cell354 OrdReceipts.checked354 (by decide) (by decide)
private theorem leaf371:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,513,some 1024⟩:=
  plain OrdReceipts.cell355 OrdReceipts.checked355 (by decide) (by decide)
private theorem leaf372:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,257,some 512⟩:=
  plain OrdReceipts.cell356 OrdReceipts.checked356 (by decide) (by decide)
private theorem leaf373:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,161,some 256⟩:=
  plain OrdReceipts.cell357 OrdReceipts.checked357 (by decide) (by decide)
private theorem leaf374:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,97,some 160⟩:=
  plain OrdReceipts.cell358 OrdReceipts.checked358 (by decide) (by decide)
private theorem leaf375:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,65,some 96⟩:=
  plain OrdReceipts.cell359 OrdReceipts.checked359 (by decide) (by decide)
private theorem leaf376:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,48,some 64⟩:=
  plain OrdReceipts.cell360 OrdReceipts.checked360 (by decide) (by decide)
private theorem leaf377:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,36,some 47⟩:=
  plain OrdReceipts.cell361 OrdReceipts.checked361 (by decide) (by decide)
private theorem leaf378:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,27,some 35⟩:=
  plain OrdReceipts.cell362 OrdReceipts.checked362 (by decide) (by decide)
private theorem leaf379:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,21,some 26⟩:=
  plain OrdReceipts.cell363 OrdReceipts.checked363 (by decide) (by decide)
private theorem leaf380:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,15,some 20⟩:=
  plain OrdReceipts.cell364 OrdReceipts.checked364 (by decide) (by decide)
private theorem leaf381:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,10,some 14⟩:=
  plain OrdReceipts.cell365 OrdReceipts.checked365 (by decide) (by decide)
private theorem leaf382:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,6,some 9⟩:=
  plain OrdReceipts.cell366 OrdReceipts.checked366 (by decide) (by decide)
private theorem leaf383:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,3,some 5⟩:=
  plain OrdReceipts.cell367 OrdReceipts.checked367 (by decide) (by decide)
private theorem leaf384:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,1,some 2⟩:=
  plain OrdReceipts.cell368 OrdReceipts.checked368 (by decide) (by decide)
private theorem leaf385:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,1,0,some 0⟩:=
  plain OrdReceipts.cell369 OrdReceipts.checked369 (by decide) (by decide)
private theorem leaf386:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,32769,none⟩:=
  plain OrdReceipts.cell370 OrdReceipts.checked370 (by decide) (by decide)
private theorem leaf387:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,16385,some 32768⟩:=
  plain OrdReceipts.cell371 OrdReceipts.checked371 (by decide) (by decide)
private theorem leaf388:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,8193,some 16384⟩:=
  plain OrdReceipts.cell372 OrdReceipts.checked372 (by decide) (by decide)
private theorem leaf389:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,4097,some 8192⟩:=
  plain OrdReceipts.cell373 OrdReceipts.checked373 (by decide) (by decide)
private theorem leaf390:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,2049,some 4096⟩:=
  plain OrdReceipts.cell374 OrdReceipts.checked374 (by decide) (by decide)
private theorem leaf391:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,1025,some 2048⟩:=
  plain OrdReceipts.cell375 OrdReceipts.checked375 (by decide) (by decide)
private theorem leaf392:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,513,some 1024⟩:=
  plain OrdReceipts.cell376 OrdReceipts.checked376 (by decide) (by decide)
private theorem leaf393:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,257,some 512⟩:=
  plain OrdReceipts.cell377 OrdReceipts.checked377 (by decide) (by decide)
private theorem leaf394:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,161,some 256⟩:=
  plain OrdReceipts.cell378 OrdReceipts.checked378 (by decide) (by decide)
private theorem leaf395:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,97,some 160⟩:=
  plain OrdReceipts.cell379 OrdReceipts.checked379 (by decide) (by decide)
private theorem leaf396:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,65,some 96⟩:=
  plain OrdReceipts.cell380 OrdReceipts.checked380 (by decide) (by decide)
private theorem leaf397:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,48,some 64⟩:=
  plain OrdReceipts.cell381 OrdReceipts.checked381 (by decide) (by decide)
private theorem leaf398:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,36,some 47⟩:=
  plain OrdReceipts.cell382 OrdReceipts.checked382 (by decide) (by decide)
private theorem leaf399:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,27,some 35⟩:=
  physical OrdReceipts.cell383 OrdReceipts.cell384 OrdReceipts.checked383 OrdReceipts.checked384 rfl 299354 (by decide) (by decide) (by decide) (by decide)
private theorem leaf400:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,21,some 26⟩:=
  plain OrdReceipts.cell385 OrdReceipts.checked385 (by decide) (by decide)
private theorem leaf401:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,15,some 20⟩:=
  plain OrdReceipts.cell386 OrdReceipts.checked386 (by decide) (by decide)
private theorem leaf402:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,10,some 14⟩:=
  plain OrdReceipts.cell387 OrdReceipts.checked387 (by decide) (by decide)
private theorem leaf403:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,6,some 9⟩:=
  plain OrdReceipts.cell388 OrdReceipts.checked388 (by decide) (by decide)
private theorem leaf404:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,3,some 5⟩:=
  plain OrdReceipts.cell389 OrdReceipts.checked389 (by decide) (by decide)
private theorem leaf405:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,1,some 2⟩:=
  plain OrdReceipts.cell390 OrdReceipts.checked390 (by decide) (by decide)
private theorem leaf406:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,2,0,some 0⟩:=
  plain OrdReceipts.cell391 OrdReceipts.checked391 (by decide) (by decide)
private theorem leaf407:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,32769,none⟩:=
  plain OrdReceipts.cell392 OrdReceipts.checked392 (by decide) (by decide)
private theorem leaf408:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,16385,some 32768⟩:=
  plain OrdReceipts.cell393 OrdReceipts.checked393 (by decide) (by decide)
private theorem leaf409:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,8193,some 16384⟩:=
  plain OrdReceipts.cell394 OrdReceipts.checked394 (by decide) (by decide)
private theorem leaf410:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,4097,some 8192⟩:=
  plain OrdReceipts.cell395 OrdReceipts.checked395 (by decide) (by decide)
private theorem leaf411:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,2049,some 4096⟩:=
  plain OrdReceipts.cell396 OrdReceipts.checked396 (by decide) (by decide)
private theorem leaf412:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,1025,some 2048⟩:=
  plain OrdReceipts.cell397 OrdReceipts.checked397 (by decide) (by decide)
private theorem leaf413:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,513,some 1024⟩:=
  plain OrdReceipts.cell398 OrdReceipts.checked398 (by decide) (by decide)
private theorem leaf414:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,257,some 512⟩:=
  plain OrdReceipts.cell399 OrdReceipts.checked399 (by decide) (by decide)
private theorem leaf415:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,161,some 256⟩:=
  plain OrdReceipts.cell400 OrdReceipts.checked400 (by decide) (by decide)
private theorem leaf416:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,97,some 160⟩:=
  plain OrdReceipts.cell401 OrdReceipts.checked401 (by decide) (by decide)
private theorem leaf417:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,65,some 96⟩:=
  plain OrdReceipts.cell402 OrdReceipts.checked402 (by decide) (by decide)
private theorem leaf418:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,48,some 64⟩:=
  plain OrdReceipts.cell403 OrdReceipts.checked403 (by decide) (by decide)
private theorem leaf419:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,36,some 47⟩:=
  plain OrdReceipts.cell404 OrdReceipts.checked404 (by decide) (by decide)
private theorem leaf420:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,27,some 35⟩:=
  plain OrdReceipts.cell405 OrdReceipts.checked405 (by decide) (by decide)
private theorem leaf421:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,24,some 26⟩:=
  plain OrdReceipts.cell406 OrdReceipts.checked406 (by decide) (by decide)
private theorem leaf422:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,21,some 23⟩:=
  plain OrdReceipts.cell407 OrdReceipts.checked407 (by decide) (by decide)
private theorem leaf423:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,18,some 20⟩:=
  plain OrdReceipts.cell408 OrdReceipts.checked408 (by decide) (by decide)
private theorem leaf424:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,17,some 17⟩:=
  plain OrdReceipts.cell409 OrdReceipts.checked409 (by decide) (by decide)
private theorem leaf425:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,15,some 16⟩:=
  plain OrdReceipts.cell410 OrdReceipts.checked410 (by decide) (by decide)
private theorem leaf426:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,10,some 14⟩:=
  plain OrdReceipts.cell411 OrdReceipts.checked411 (by decide) (by decide)
private theorem leaf427:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,6,some 9⟩:=
  plain OrdReceipts.cell412 OrdReceipts.checked412 (by decide) (by decide)
private theorem leaf428:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,3,some 5⟩:=
  plain OrdReceipts.cell413 OrdReceipts.checked413 (by decide) (by decide)
private theorem leaf429:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,1,some 2⟩:=
  plain OrdReceipts.cell414 OrdReceipts.checked414 (by decide) (by decide)
private theorem leaf430:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,3,0,some 0⟩:=
  plain OrdReceipts.cell415 OrdReceipts.checked415 (by decide) (by decide)
private theorem leaf431:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,32769,none⟩:=
  plain OrdReceipts.cell416 OrdReceipts.checked416 (by decide) (by decide)
private theorem leaf432:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,16385,some 32768⟩:=
  plain OrdReceipts.cell417 OrdReceipts.checked417 (by decide) (by decide)
private theorem leaf433:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,8193,some 16384⟩:=
  plain OrdReceipts.cell418 OrdReceipts.checked418 (by decide) (by decide)
private theorem leaf434:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,4097,some 8192⟩:=
  plain OrdReceipts.cell419 OrdReceipts.checked419 (by decide) (by decide)
private theorem leaf435:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,2049,some 4096⟩:=
  plain OrdReceipts.cell420 OrdReceipts.checked420 (by decide) (by decide)
private theorem leaf436:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,1025,some 2048⟩:=
  plain OrdReceipts.cell421 OrdReceipts.checked421 (by decide) (by decide)
private theorem leaf437:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,513,some 1024⟩:=
  plain OrdReceipts.cell422 OrdReceipts.checked422 (by decide) (by decide)
private theorem leaf438:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,257,some 512⟩:=
  plain OrdReceipts.cell423 OrdReceipts.checked423 (by decide) (by decide)
private theorem leaf439:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,161,some 256⟩:=
  plain OrdReceipts.cell424 OrdReceipts.checked424 (by decide) (by decide)
private theorem leaf440:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,97,some 160⟩:=
  plain OrdReceipts.cell425 OrdReceipts.checked425 (by decide) (by decide)
private theorem leaf441:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,65,some 96⟩:=
  plain OrdReceipts.cell426 OrdReceipts.checked426 (by decide) (by decide)
private theorem leaf442:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,48,some 64⟩:=
  plain OrdReceipts.cell427 OrdReceipts.checked427 (by decide) (by decide)
private theorem leaf443:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,36,some 47⟩:=
  plain OrdReceipts.cell428 OrdReceipts.checked428 (by decide) (by decide)
private theorem leaf444:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,27,some 35⟩:=
  plain OrdReceipts.cell429 OrdReceipts.checked429 (by decide) (by decide)
private theorem leaf445:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,21,some 26⟩:=
  plain OrdReceipts.cell430 OrdReceipts.checked430 (by decide) (by decide)
private theorem leaf446:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,15,some 20⟩:=
  plain OrdReceipts.cell431 OrdReceipts.checked431 (by decide) (by decide)
private theorem leaf447:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,10,some 14⟩:=
  plain OrdReceipts.cell432 OrdReceipts.checked432 (by decide) (by decide)
private theorem leaf448:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,6,some 9⟩:=
  plain OrdReceipts.cell433 OrdReceipts.checked433 (by decide) (by decide)
private theorem leaf449:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,3,some 5⟩:=
  plain OrdReceipts.cell434 OrdReceipts.checked434 (by decide) (by decide)
private theorem leaf450:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,1,some 2⟩:=
  plain OrdReceipts.cell435 OrdReceipts.checked435 (by decide) (by decide)
private theorem leaf451:Done 2314 2411 OrdinaryBooks.near 351 ⟨28,32,9,4,0,some 0⟩:=
  plain OrdReceipts.cell436 OrdReceipts.checked436 (by decide) (by decide)
private theorem tail1_32769:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 32769:=leaf365
private theorem tail1_16385:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 16385:=join leaf366 tail1_32769
private theorem tail1_8193:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 8193:=join leaf367 tail1_16385
private theorem tail1_4097:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 4097:=join leaf368 tail1_8193
private theorem tail1_2049:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 2049:=join leaf369 tail1_4097
private theorem tail1_1025:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 1025:=join leaf370 tail1_2049
private theorem tail1_513:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 513:=join leaf371 tail1_1025
private theorem tail1_257:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 257:=join leaf372 tail1_513
private theorem tail1_161:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 161:=join leaf373 tail1_257
private theorem tail1_97:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 97:=join leaf374 tail1_161
private theorem tail1_65:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 65:=join leaf375 tail1_97
private theorem tail1_48:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 48:=join leaf376 tail1_65
private theorem tail1_36:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 36:=join leaf377 tail1_48
private theorem tail1_27:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 27:=join leaf378 tail1_36
private theorem tail1_21:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 21:=join leaf379 tail1_27
private theorem tail1_15:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 15:=join leaf380 tail1_21
private theorem tail1_10:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 10:=join leaf381 tail1_15
private theorem tail1_6:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 6:=join leaf382 tail1_10
private theorem tail1_3:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 3:=join leaf383 tail1_6
private theorem tail1_1:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 1:=join leaf384 tail1_3
private theorem tail1_0:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 1 0:=join leaf385 tail1_1
private theorem tail2_32769:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 32769:=leaf386
private theorem tail2_16385:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 16385:=join leaf387 tail2_32769
private theorem tail2_8193:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 8193:=join leaf388 tail2_16385
private theorem tail2_4097:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 4097:=join leaf389 tail2_8193
private theorem tail2_2049:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 2049:=join leaf390 tail2_4097
private theorem tail2_1025:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 1025:=join leaf391 tail2_2049
private theorem tail2_513:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 513:=join leaf392 tail2_1025
private theorem tail2_257:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 257:=join leaf393 tail2_513
private theorem tail2_161:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 161:=join leaf394 tail2_257
private theorem tail2_97:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 97:=join leaf395 tail2_161
private theorem tail2_65:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 65:=join leaf396 tail2_97
private theorem tail2_48:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 48:=join leaf397 tail2_65
private theorem tail2_36:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 36:=join leaf398 tail2_48
private theorem tail2_27:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 27:=join leaf399 tail2_36
private theorem tail2_21:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 21:=join leaf400 tail2_27
private theorem tail2_15:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 15:=join leaf401 tail2_21
private theorem tail2_10:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 10:=join leaf402 tail2_15
private theorem tail2_6:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 6:=join leaf403 tail2_10
private theorem tail2_3:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 3:=join leaf404 tail2_6
private theorem tail2_1:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 1:=join leaf405 tail2_3
private theorem tail2_0:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 2 0:=join leaf406 tail2_1
private theorem tail3_32769:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 32769:=leaf407
private theorem tail3_16385:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 16385:=join leaf408 tail3_32769
private theorem tail3_8193:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 8193:=join leaf409 tail3_16385
private theorem tail3_4097:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 4097:=join leaf410 tail3_8193
private theorem tail3_2049:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 2049:=join leaf411 tail3_4097
private theorem tail3_1025:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 1025:=join leaf412 tail3_2049
private theorem tail3_513:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 513:=join leaf413 tail3_1025
private theorem tail3_257:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 257:=join leaf414 tail3_513
private theorem tail3_161:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 161:=join leaf415 tail3_257
private theorem tail3_97:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 97:=join leaf416 tail3_161
private theorem tail3_65:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 65:=join leaf417 tail3_97
private theorem tail3_48:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 48:=join leaf418 tail3_65
private theorem tail3_36:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 36:=join leaf419 tail3_48
private theorem tail3_27:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 27:=join leaf420 tail3_36
private theorem tail3_24:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 24:=join leaf421 tail3_27
private theorem tail3_21:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 21:=join leaf422 tail3_24
private theorem tail3_18:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 18:=join leaf423 tail3_21
private theorem tail3_17:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 17:=join leaf424 tail3_18
private theorem tail3_15:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 15:=join leaf425 tail3_17
private theorem tail3_10:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 10:=join leaf426 tail3_15
private theorem tail3_6:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 6:=join leaf427 tail3_10
private theorem tail3_3:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 3:=join leaf428 tail3_6
private theorem tail3_1:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 1:=join leaf429 tail3_3
private theorem tail3_0:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 3 0:=join leaf430 tail3_1
private theorem tail4_32769:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 32769:=leaf431
private theorem tail4_16385:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 16385:=join leaf432 tail4_32769
private theorem tail4_8193:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 8193:=join leaf433 tail4_16385
private theorem tail4_4097:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 4097:=join leaf434 tail4_8193
private theorem tail4_2049:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 2049:=join leaf435 tail4_4097
private theorem tail4_1025:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 1025:=join leaf436 tail4_2049
private theorem tail4_513:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 513:=join leaf437 tail4_1025
private theorem tail4_257:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 257:=join leaf438 tail4_513
private theorem tail4_161:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 161:=join leaf439 tail4_257
private theorem tail4_97:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 97:=join leaf440 tail4_161
private theorem tail4_65:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 65:=join leaf441 tail4_97
private theorem tail4_48:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 48:=join leaf442 tail4_65
private theorem tail4_36:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 36:=join leaf443 tail4_48
private theorem tail4_27:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 27:=join leaf444 tail4_36
private theorem tail4_21:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 21:=join leaf445 tail4_27
private theorem tail4_15:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 15:=join leaf446 tail4_21
private theorem tail4_10:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 10:=join leaf447 tail4_15
private theorem tail4_6:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 6:=join leaf448 tail4_10
private theorem tail4_3:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 3:=join leaf449 tail4_6
private theorem tail4_1:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 1:=join leaf450 tail4_3
private theorem tail4_0:Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 4 0:=join leaf451 tail4_1
theorem allDegrees (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail 2314 2411 OrdinaryBooks.near 351 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0
  · exact tail2_0
  · exact tail3_0
  · exact tail4_0
end Research6969.OrdRouteNear3
end Z6969Source0935

end Merged_Z6969Pack0655

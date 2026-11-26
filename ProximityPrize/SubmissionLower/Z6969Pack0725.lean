import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0725
section Merged_Z6969Pack0725

-- Source: Research6969.PrefixMiddleSaved75
section Z6969Source1748
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved75
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle75.price Lower6960.Prefix6969RescueData.Middle75.price :=
  ⟨335, 3285, 50, 734, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle75.plan Lower6960.Prefix6969RescueData.Middle75.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 51 56 :=
  ⟨Lower6960.Prefix6969MainCases.Middle75.plan, Lower6960.Prefix6969MainCases.Middle75.price, Lower6960.Prefix6969MainCases.Middle75.valid, Lower6960.Prefix6969MainCases.Middle75.priced, Lower6960.Prefix6969MainCases.Middle75.sources,
   Lower6960.Prefix6969RescueData.Middle75.plan, Lower6960.Prefix6969RescueData.Middle75.price, Lower6960.Prefix6969RescueData.Middle75.sources, Lower6960.Prefix6969RescueData.Middle75.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved75
end Z6969Source1748

-- Source: Research6969.PhysicalChecks172
section Z6969Source1749
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2752 : Request := ⟨⟨⟨556,772,170,6016⟩,5255817068544,9968090926⟩,10,3,2,385609,11⟩
private theorem pass2752_2390 : (Triangular src2752) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2752_2391 : (Triangular src2752) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2752_2393 : (Triangular src2752) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2752_2399 : (Triangular src2752) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2752_2417 : (Triangular src2752) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2752_2469 : (Triangular src2752) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2752 : Cover (Triangular src2752) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2752_2390, by decide, by decide, pass2752_2391, by decide, by decide, pass2752_2393, by decide, by decide, pass2752_2399, by decide, by decide, pass2752_2417, by decide, by decide, pass2752_2469, rfl⟩
def src2753 : Request := ⟨⟨⟨556,772,170,5936⟩,5255817068544,9968090926⟩,10,3,2,385609,12⟩
private theorem pass2753_2390 : (Triangular src2753) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2753_2391 : (Triangular src2753) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2753_2393 : (Triangular src2753) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2753_2399 : (Triangular src2753) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2753_2417 : (Triangular src2753) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2753_2469 : (Triangular src2753) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2753 : Cover (Triangular src2753) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2753_2390, by decide, by decide, pass2753_2391, by decide, by decide, pass2753_2393, by decide, by decide, pass2753_2399, by decide, by decide, pass2753_2417, by decide, by decide, pass2753_2469, rfl⟩
def src2754 : Request := ⟨⟨⟨556,772,170,5857⟩,5255817068544,9968090926⟩,10,3,2,385609,13⟩
private theorem pass2754_2390 : (Triangular src2754) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2754_2391 : (Triangular src2754) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2754_2393 : (Triangular src2754) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2754_2399 : (Triangular src2754) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2754_2417 : (Triangular src2754) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2754_2469 : (Triangular src2754) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2754 : Cover (Triangular src2754) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2754_2390, by decide, by decide, pass2754_2391, by decide, by decide, pass2754_2393, by decide, by decide, pass2754_2399, by decide, by decide, pass2754_2417, by decide, by decide, pass2754_2469, rfl⟩
def src2755 : Request := ⟨⟨⟨556,772,170,5779⟩,5255817068544,9968090926⟩,10,3,2,385609,14⟩
private theorem pass2755_2390 : (Triangular src2755) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2755_2391 : (Triangular src2755) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2755_2393 : (Triangular src2755) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2755_2399 : (Triangular src2755) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2755_2417 : (Triangular src2755) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2755_2469 : (Triangular src2755) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2755 : Cover (Triangular src2755) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2755_2390, by decide, by decide, pass2755_2391, by decide, by decide, pass2755_2393, by decide, by decide, pass2755_2399, by decide, by decide, pass2755_2417, by decide, by decide, pass2755_2469, rfl⟩
def src2756 : Request := ⟨⟨⟨556,772,170,5702⟩,5255817068544,9968090926⟩,10,3,2,385609,15⟩
private theorem pass2756_2390 : (Triangular src2756) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2756_2391 : (Triangular src2756) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2756_2394 : (Triangular src2756) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2756_2402 : (Triangular src2756) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2756_2426 : (Triangular src2756) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2756_2496 : (Triangular src2756) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2756 : Cover (Triangular src2756) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2756_2390, by decide, by decide, pass2756_2391, by decide, by decide, pass2756_2394, by decide, by decide, pass2756_2402, by decide, by decide, pass2756_2426, by decide, by decide, pass2756_2496, rfl⟩
def src2757 : Request := ⟨⟨⟨556,772,170,5625⟩,5255817068544,9968090926⟩,10,3,2,385609,16⟩
private theorem pass2757_2390 : (Triangular src2757) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2757_2391 : (Triangular src2757) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2757_2393 : (Triangular src2757) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2757_2399 : (Triangular src2757) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2757_2417 : (Triangular src2757) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2757_2469 : (Triangular src2757) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2757 : Cover (Triangular src2757) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2757_2390, by decide, by decide, pass2757_2391, by decide, by decide, pass2757_2393, by decide, by decide, pass2757_2399, by decide, by decide, pass2757_2417, by decide, by decide, pass2757_2469, rfl⟩
def src2758 : Request := ⟨⟨⟨556,772,170,5550⟩,5255817068544,9968090926⟩,10,3,2,385609,17⟩
private theorem pass2758_2390 : (Triangular src2758) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2758_2391 : (Triangular src2758) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2758_2394 : (Triangular src2758) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2758_2402 : (Triangular src2758) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2758_2426 : (Triangular src2758) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2758_2496 : (Triangular src2758) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2758 : Cover (Triangular src2758) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2758_2390, by decide, by decide, pass2758_2391, by decide, by decide, pass2758_2394, by decide, by decide, pass2758_2402, by decide, by decide, pass2758_2426, by decide, by decide, pass2758_2496, rfl⟩
def src2759 : Request := ⟨⟨⟨556,772,170,5475⟩,5255817068544,9968090926⟩,10,3,2,385609,18⟩
private theorem pass2759_2390 : (Triangular src2759) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2759_2391 : (Triangular src2759) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2759_2393 : (Triangular src2759) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2759_2399 : (Triangular src2759) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2759_2417 : (Triangular src2759) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2759_2469 : (Triangular src2759) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2759 : Cover (Triangular src2759) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2759_2390, by decide, by decide, pass2759_2391, by decide, by decide, pass2759_2393, by decide, by decide, pass2759_2399, by decide, by decide, pass2759_2417, by decide, by decide, pass2759_2469, rfl⟩
def src2760 : Request := ⟨⟨⟨556,772,170,5402⟩,5255817068544,9968090926⟩,10,3,2,385609,19⟩
private theorem pass2760_2390 : (Triangular src2760) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2760_2391 : (Triangular src2760) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2760_2394 : (Triangular src2760) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2760_2402 : (Triangular src2760) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2760_2426 : (Triangular src2760) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2760_2496 : (Triangular src2760) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2760 : Cover (Triangular src2760) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2760_2390, by decide, by decide, pass2760_2391, by decide, by decide, pass2760_2394, by decide, by decide, pass2760_2402, by decide, by decide, pass2760_2426, by decide, by decide, pass2760_2496, rfl⟩
def src2761 : Request := ⟨⟨⟨556,772,170,5329⟩,5255817068544,9968090926⟩,10,3,2,385609,20⟩
private theorem pass2761_2390 : (Triangular src2761) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2761_2391 : (Triangular src2761) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2761_2393 : (Triangular src2761) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2761_2399 : (Triangular src2761) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2761_2417 : (Triangular src2761) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2761_2469 : (Triangular src2761) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2761 : Cover (Triangular src2761) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2761_2390, by decide, by decide, pass2761_2391, by decide, by decide, pass2761_2393, by decide, by decide, pass2761_2399, by decide, by decide, pass2761_2417, by decide, by decide, pass2761_2469, rfl⟩
def src2762 : Request := ⟨⟨⟨556,772,170,5258⟩,5255817068544,9968090926⟩,10,3,2,385609,21⟩
private theorem pass2762_2390 : (Triangular src2762) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2762_2391 : (Triangular src2762) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2762_2394 : (Triangular src2762) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2762_2402 : (Triangular src2762) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2762_2426 : (Triangular src2762) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2762_2496 : (Triangular src2762) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2762 : Cover (Triangular src2762) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2762_2390, by decide, by decide, pass2762_2391, by decide, by decide, pass2762_2394, by decide, by decide, pass2762_2402, by decide, by decide, pass2762_2426, by decide, by decide, pass2762_2496, rfl⟩
def src2763 : Request := ⟨⟨⟨556,772,170,5187⟩,5255817068544,9968090926⟩,10,3,2,385609,22⟩
private theorem pass2763_2390 : (Triangular src2763) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2763_2391 : (Triangular src2763) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2763_2393 : (Triangular src2763) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2763_2399 : (Triangular src2763) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2763_2417 : (Triangular src2763) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2763_2469 : (Triangular src2763) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2763 : Cover (Triangular src2763) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2763_2390, by decide, by decide, pass2763_2391, by decide, by decide, pass2763_2393, by decide, by decide, pass2763_2399, by decide, by decide, pass2763_2417, by decide, by decide, pass2763_2469, rfl⟩
def src2764 : Request := ⟨⟨⟨556,772,170,5118⟩,5255817068544,9968090926⟩,10,3,2,385609,23⟩
private theorem pass2764_2390 : (Triangular src2764) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2764_2391 : (Triangular src2764) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2764_2393 : (Triangular src2764) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2764_2399 : (Triangular src2764) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2764_2417 : (Triangular src2764) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2764_2469 : (Triangular src2764) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2764 : Cover (Triangular src2764) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2764_2390, by decide, by decide, pass2764_2391, by decide, by decide, pass2764_2393, by decide, by decide, pass2764_2399, by decide, by decide, pass2764_2417, by decide, by decide, pass2764_2469, rfl⟩
def src2765 : Request := ⟨⟨⟨556,772,170,5050⟩,5255817068544,9968090926⟩,10,3,2,385609,24⟩
private theorem pass2765_2390 : (Triangular src2765) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2765_2391 : (Triangular src2765) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2765_2393 : (Triangular src2765) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2765_2399 : (Triangular src2765) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2765_2417 : (Triangular src2765) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2765_2469 : (Triangular src2765) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2765 : Cover (Triangular src2765) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2765_2390, by decide, by decide, pass2765_2391, by decide, by decide, pass2765_2393, by decide, by decide, pass2765_2399, by decide, by decide, pass2765_2417, by decide, by decide, pass2765_2469, rfl⟩
def src2766 : Request := ⟨⟨⟨556,772,170,4983⟩,5255817068544,9968090926⟩,10,3,2,385609,25⟩
private theorem pass2766_2390 : (Triangular src2766) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2766_2391 : (Triangular src2766) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2766_2393 : (Triangular src2766) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2766_2399 : (Triangular src2766) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2766_2417 : (Triangular src2766) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2766_2469 : (Triangular src2766) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2766 : Cover (Triangular src2766) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2766_2390, by decide, by decide, pass2766_2391, by decide, by decide, pass2766_2393, by decide, by decide, pass2766_2399, by decide, by decide, pass2766_2417, by decide, by decide, pass2766_2469, rfl⟩
def src2767 : Request := ⟨⟨⟨556,772,170,4918⟩,5255817068544,9968090926⟩,10,3,2,385609,26⟩
private theorem pass2767_2390 : (Triangular src2767) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2767_2391 : (Triangular src2767) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2767_2394 : (Triangular src2767) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2767_2402 : (Triangular src2767) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2767_2426 : (Triangular src2767) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2767_2496 : (Triangular src2767) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2767 : Cover (Triangular src2767) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2767_2390, by decide, by decide, pass2767_2391, by decide, by decide, pass2767_2394, by decide, by decide, pass2767_2402, by decide, by decide, pass2767_2426, by decide, by decide, pass2767_2496, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1749

-- Source: Research6969.PrefixMainDataMiddle76
section Z6969Source1750
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle76
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank186 19684, bank176 24684, bank170 28384, bank212 8810] i
  head := src2761
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15027, 126203, 585943, 2149545],
    ![12303, 99386, 898709/2, 3224045/2],
    ![53398/9, 432061/9, 898709/2, 3224045/2],
    ![29433/8, 467827/16, 2117714/9, 831324],
    ![63824/25, 505633/25, 313709/2, 2253001/4],
    ![72196/49, 573817/49, 2586181/25, 9133906/25],
    ![40539/50, 676511/100, 71355, 1134225/4],
    ![95180/121, 722210/121, 464048/7, 10945766/49],
    ![95180/121, 722210/121, 116003/2, 870489/4],
    ![63754/121, 755842/147, 770661/16, 10503459/49],
    ![63754/121, 755842/147, 770661/16, 596848/3],
    ![63754/121, 609747/121, 770661/16, 32176502/225],
    ![1355575/3362, 609747/121, 770661/16, 32176502/225],
    ![1355575/3362, 7244984/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 589390/147, 4332756/121, 27028688/225],
    ![481425/1369, 589390/147, 4332756/121, 27028688/225],
    ![466774/1369, 589390/147, 4332756/121, 27028688/225],
    ![920087/2738, 589390/147, 4332756/121, 27028688/225],
    ![920087/2738, 21189861/5476, 95170565/2704, 27028688/225]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 19 257073 := by
  refine ⟨?_, rank154 5329, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2761⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free49_1
    · exact free58_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free126_1
    · exact free153_1
    · exact free199_1
    · exact free186_1
    · exact free176_1
    · exact free170_1
    · exact free212_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [255663399, 332700328, 331974128, 332068544, 331551260, 331747343, 331972242, 146240031, 146597514, 146789285, 146522942, 73032174, 73063202, 70079688, 101033294, 100425148, 150823316, 101057369, 233826221], [1418680, 1035798, 1037790, 1037531, 1038950, 1038412, 1037795, 2635990, 2628143, 2623934, 2629780, 5491080, 5488612, 5725991, 3915291, 3940986, 2555963, 3914274, 1582893],
  ![124119634631220, 1608116572024, 210443598900, 5840510820], 141924572451338048⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 21189861/5476, 95170565/2704, 27028688/225] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle76
end Z6969Source1750

-- Source: Research6969.PhysicalChecks128
section Z6969Source1751
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2048 : Request := ⟨⟨⟨2100,2930,632,29839⟩,278060332482560,2019119590628⟩,3,2,1,257073,18⟩
private theorem pass2048_2390 : (Triangular src2048) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2048_2391 : (Triangular src2048) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2048_2393 : (Triangular src2048) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2048_2398 : (Triangular src2048) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2048_2412 : (Triangular src2048) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2048_2449 : (Triangular src2048) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2048 : Cover (Triangular src2048) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2048_2390, by decide, by decide, pass2048_2391, by decide, by decide, pass2048_2393, by decide, by decide, pass2048_2398, by decide, by decide, pass2048_2412, by decide, by decide, pass2048_2449, rfl⟩
def src2049 : Request := ⟨⟨⟨1750,2442,527,28917⟩,161065121873920,975196209190⟩,4,2,1,257073,18⟩
private theorem pass2049_2390 : (Triangular src2049) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2049_2391 : (Triangular src2049) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2049_2393 : (Triangular src2049) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2049_2398 : (Triangular src2049) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2049_2412 : (Triangular src2049) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2049_2449 : (Triangular src2049) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2049 : Cover (Triangular src2049) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2049_2390, by decide, by decide, pass2049_2391, by decide, by decide, pass2049_2393, by decide, by decide, pass2049_2398, by decide, by decide, pass2049_2412, by decide, by decide, pass2049_2449, rfl⟩
def src2050 : Request := ⟨⟨⟨2100,2930,632,30948⟩,278060332482560,2019119590628⟩,4,2,1,257073,18⟩
private theorem pass2050_2390 : (Triangular src2050) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2050_2391 : (Triangular src2050) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2050_2393 : (Triangular src2050) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2050_2398 : (Triangular src2050) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2050_2412 : (Triangular src2050) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2050_2449 : (Triangular src2050) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2050 : Cover (Triangular src2050) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2050_2390, by decide, by decide, pass2050_2391, by decide, by decide, pass2050_2393, by decide, by decide, pass2050_2398, by decide, by decide, pass2050_2412, by decide, by decide, pass2050_2449, rfl⟩
def src2051 : Request := ⟨⟨⟨2600,3628,783,39053⟩,527755772952576,4745819470168⟩,8,2,1,257073,18⟩
private theorem pass2051_2390 : (Triangular src2051) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2051_2391 : (Triangular src2051) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2051_2393 : (Triangular src2051) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2051_2398 : (Triangular src2051) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2051_2412 : (Triangular src2051) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2051_2448 : (Triangular src2051) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2051 : Cover (Triangular src2051) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2051_2390, by decide, by decide, pass2051_2391, by decide, by decide, pass2051_2393, by decide, by decide, pass2051_2398, by decide, by decide, pass2051_2412, by decide, by decide, pass2051_2448, rfl⟩
def src2052 : Request := ⟨⟨⟨3200,4465,963,45637⟩,983050615259136,10877088344236⟩,10,2,1,257073,18⟩
private theorem pass2052_2390 : (Triangular src2052) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2052_2391 : (Triangular src2052) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2052_2393 : (Triangular src2052) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2052_2398 : (Triangular src2052) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2052_2411 : (Triangular src2052) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2052_2446 : (Triangular src2052) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2052 : Cover (Triangular src2052) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2052_2390, by decide, by decide, pass2052_2391, by decide, by decide, pass2052_2393, by decide, by decide, pass2052_2398, by decide, by decide, pass2052_2411, by decide, by decide, pass2052_2446, rfl⟩
def src2053 : Request := ⟨⟨⟨3200,4465,963,49146⟩,983050615259136,10877088344236⟩,13,2,1,257073,18⟩
private theorem pass2053_2390 : (Triangular src2053) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2053_2391 : (Triangular src2053) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2053_2393 : (Triangular src2053) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2053_2398 : (Triangular src2053) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2053_2411 : (Triangular src2053) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2053_2446 : (Triangular src2053) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2053 : Cover (Triangular src2053) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2053_2390, by decide, by decide, pass2053_2391, by decide, by decide, pass2053_2393, by decide, by decide, pass2053_2398, by decide, by decide, pass2053_2411, by decide, by decide, pass2053_2446, rfl⟩
def src2054 : Request := ⟨⟨⟨4800,6698,1445,84978⟩,3317023033262080,55058665830093⟩,32,2,1,257073,18⟩
private theorem pass2054_2390 : (Triangular src2054) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2054_2391 : (Triangular src2054) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2054_2393 : (Triangular src2054) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2054_2398 : (Triangular src2054) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2054_2411 : (Triangular src2054) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2054_2445 : (Triangular src2054) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2054_2534 : (Triangular src2054) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2054 : Cover (Triangular src2054) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2054_2390, by decide, by decide, pass2054_2391, by decide, by decide, pass2054_2393, by decide, by decide, pass2054_2398, by decide, by decide, pass2054_2411, by decide, by decide, pass2054_2445, by decide, by decide, pass2054_2534, rfl⟩
def src2055 : Request := ⟨⟨⟨5700,7954,1716,88754⟩,5553838907981824,109473260530676⟩,32,2,1,257073,18⟩
private theorem pass2055_2390 : (Triangular src2055) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2055_2391 : (Triangular src2055) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2055_2393 : (Triangular src2055) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2055_2398 : (Triangular src2055) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2055_2411 : (Triangular src2055) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2055_2445 : (Triangular src2055) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2055_2533 : (Triangular src2055) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2055 : Cover (Triangular src2055) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2055_2390, by decide, by decide, pass2055_2391, by decide, by decide, pass2055_2393, by decide, by decide, pass2055_2398, by decide, by decide, pass2055_2411, by decide, by decide, pass2055_2445, by decide, by decide, pass2055_2533, rfl⟩
def src2056 : Request := ⟨⟨⟨1450,2023,436,19562⟩,91566841790464,459151377566⟩,0,2,1,257073,19⟩
private theorem pass2056_2390 : (Triangular src2056) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2056_2391 : (Triangular src2056) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2056_2393 : (Triangular src2056) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2056_2399 : (Triangular src2056) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2056_2415 : (Triangular src2056) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2056_2458 : (Triangular src2056) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2056 : Cover (Triangular src2056) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2056_2390, by decide, by decide, pass2056_2391, by decide, by decide, pass2056_2393, by decide, by decide, pass2056_2399, by decide, by decide, pass2056_2415, by decide, by decide, pass2056_2458, rfl⟩
def src2057 : Request := ⟨⟨⟨1750,2442,527,22518⟩,161065121873920,975196209190⟩,1,2,1,257073,19⟩
private theorem pass2057_2390 : (Triangular src2057) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2057_2391 : (Triangular src2057) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2057_2393 : (Triangular src2057) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2057_2399 : (Triangular src2057) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2057_2415 : (Triangular src2057) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2057_2457 : (Triangular src2057) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2057 : Cover (Triangular src2057) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2057_2390, by decide, by decide, pass2057_2391, by decide, by decide, pass2057_2393, by decide, by decide, pass2057_2399, by decide, by decide, pass2057_2415, by decide, by decide, pass2057_2457, rfl⟩
def src2058 : Request := ⟨⟨⟨2100,2930,632,26836⟩,278060332482560,2019119590628⟩,3,2,1,257073,19⟩
private theorem pass2058_2390 : (Triangular src2058) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2058_2391 : (Triangular src2058) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2058_2393 : (Triangular src2058) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2058_2398 : (Triangular src2058) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2058_2412 : (Triangular src2058) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2058_2449 : (Triangular src2058) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2058 : Cover (Triangular src2058) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2058_2390, by decide, by decide, pass2058_2391, by decide, by decide, pass2058_2393, by decide, by decide, pass2058_2398, by decide, by decide, pass2058_2412, by decide, by decide, pass2058_2449, rfl⟩
def src2059 : Request := ⟨⟨⟨2100,2930,632,27758⟩,278060332482560,2019119590628⟩,4,2,1,257073,19⟩
private theorem pass2059_2390 : (Triangular src2059) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2059_2391 : (Triangular src2059) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2059_2393 : (Triangular src2059) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2059_2398 : (Triangular src2059) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2059_2412 : (Triangular src2059) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2059_2449 : (Triangular src2059) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2059 : Cover (Triangular src2059) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2059_2390, by decide, by decide, pass2059_2391, by decide, by decide, pass2059_2393, by decide, by decide, pass2059_2398, by decide, by decide, pass2059_2412, by decide, by decide, pass2059_2449, rfl⟩
def src2060 : Request := ⟨⟨⟨2600,3628,783,34973⟩,527755772952576,4745819470168⟩,8,2,1,257073,19⟩
private theorem pass2060_2390 : (Triangular src2060) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2060_2391 : (Triangular src2060) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2060_2393 : (Triangular src2060) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2060_2398 : (Triangular src2060) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2060_2412 : (Triangular src2060) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2060_2448 : (Triangular src2060) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2060 : Cover (Triangular src2060) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2060_2390, by decide, by decide, pass2060_2391, by decide, by decide, pass2060_2393, by decide, by decide, pass2060_2398, by decide, by decide, pass2060_2412, by decide, by decide, pass2060_2448, rfl⟩
def src2061 : Request := ⟨⟨⟨3200,4465,963,43957⟩,983050615259136,10877088344236⟩,13,2,1,257073,19⟩
private theorem pass2061_2390 : (Triangular src2061) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2061_2391 : (Triangular src2061) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2061_2393 : (Triangular src2061) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2061_2398 : (Triangular src2061) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2061_2411 : (Triangular src2061) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2061_2446 : (Triangular src2061) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2061 : Cover (Triangular src2061) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2061_2390, by decide, by decide, pass2061_2391, by decide, by decide, pass2061_2393, by decide, by decide, pass2061_2398, by decide, by decide, pass2061_2411, by decide, by decide, pass2061_2446, rfl⟩
def src2062 : Request := ⟨⟨⟨5700,7954,1716,79307⟩,5553838907981824,109473260530676⟩,32,2,1,257073,19⟩
private theorem pass2062_2390 : (Triangular src2062) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2062_2391 : (Triangular src2062) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2062_2393 : (Triangular src2062) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2062_2398 : (Triangular src2062) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2062_2411 : (Triangular src2062) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2062_2445 : (Triangular src2062) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2062_2533 : (Triangular src2062) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2062 : Cover (Triangular src2062) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2062_2390, by decide, by decide, pass2062_2391, by decide, by decide, pass2062_2393, by decide, by decide, pass2062_2398, by decide, by decide, pass2062_2411, by decide, by decide, pass2062_2445, by decide, by decide, pass2062_2533, rfl⟩
def src2063 : Request := ⟨⟨⟨6900,9628,2077,136716⟩,9849424459857920,234966243278304⟩,65,2,1,257073,19⟩
private theorem pass2063_2390 : (Triangular src2063) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2063_2391 : (Triangular src2063) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2063_2393 : (Triangular src2063) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2063_2398 : (Triangular src2063) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2063_2411 : (Triangular src2063) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2063_2445 : (Triangular src2063) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2063_2533 : (Triangular src2063) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2063 : Cover (Triangular src2063) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2063_2390, by decide, by decide, pass2063_2391, by decide, by decide, pass2063_2393, by decide, by decide, pass2063_2398, by decide, by decide, pass2063_2411, by decide, by decide, pass2063_2445, by decide, by decide, pass2063_2533, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1751

-- Source: Research6969.PhysicalChecks129
section Z6969Source1752
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2064 : Request := ⟨⟨⟨8300,11582,2498,133661⟩,17139238515245056,491880571317053⟩,65,2,1,257073,19⟩
private theorem pass2064_2390 : (Triangular src2064) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2064_2391 : (Triangular src2064) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2064_2393 : (Triangular src2064) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2064_2398 : (Triangular src2064) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2064_2411 : (Triangular src2064) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2064_2445 : (Triangular src2064) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2064_2533 : (Triangular src2064) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2064 : Cover (Triangular src2064) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2064_2390, by decide, by decide, pass2064_2391, by decide, by decide, pass2064_2393, by decide, by decide, pass2064_2398, by decide, by decide, pass2064_2411, by decide, by decide, pass2064_2445, by decide, by decide, pass2064_2533, rfl⟩
def src2065 : Request := ⟨⟨⟨10000,13955,3010,140635⟩,29974681586237440,1036603432174989⟩,65,2,1,257073,19⟩
private theorem pass2065_2390 : (Triangular src2065) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2065_2391 : (Triangular src2065) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2065_2393 : (Triangular src2065) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2065_2398 : (Triangular src2065) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2065_2411 : (Triangular src2065) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2065_2445 : (Triangular src2065) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2065_2533 : (Triangular src2065) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2065 : Cover (Triangular src2065) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2065_2390, by decide, by decide, pass2065_2391, by decide, by decide, pass2065_2393, by decide, by decide, pass2065_2398, by decide, by decide, pass2065_2411, by decide, by decide, pass2065_2445, by decide, by decide, pass2065_2533, rfl⟩
def src2066 : Request := ⟨⟨⟨1450,2023,436,17554⟩,91566841790464,459151377566⟩,0,2,1,257073,20⟩
private theorem pass2066_2390 : (Triangular src2066) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2066_2391 : (Triangular src2066) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2066_2393 : (Triangular src2066) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2066_2399 : (Triangular src2066) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2066_2415 : (Triangular src2066) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2066_2458 : (Triangular src2066) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2066 : Cover (Triangular src2066) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2066_2390, by decide, by decide, pass2066_2391, by decide, by decide, pass2066_2393, by decide, by decide, pass2066_2399, by decide, by decide, pass2066_2415, by decide, by decide, pass2066_2458, rfl⟩
def src2067 : Request := ⟨⟨⟨1450,2023,436,18436⟩,91566841790464,459151377566⟩,1,2,1,257073,20⟩
private theorem pass2067_2390 : (Triangular src2067) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2067_2391 : (Triangular src2067) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2067_2393 : (Triangular src2067) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2067_2399 : (Triangular src2067) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2067_2415 : (Triangular src2067) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2067_2458 : (Triangular src2067) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2067 : Cover (Triangular src2067) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2067_2390, by decide, by decide, pass2067_2391, by decide, by decide, pass2067_2393, by decide, by decide, pass2067_2399, by decide, by decide, pass2067_2415, by decide, by decide, pass2067_2458, rfl⟩
def src2068 : Request := ⟨⟨⟨1750,2442,537,20387⟩,163381988556800,989573241440⟩,2,2,1,257073,20⟩
private theorem pass2068_2390 : (Triangular src2068) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2068_2391 : (Triangular src2068) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2068_2393 : (Triangular src2068) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2068_2398 : (Triangular src2068) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2068_2412 : (Triangular src2068) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2068_2449 : (Triangular src2068) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2068 : Cover (Triangular src2068) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2068_2390, by decide, by decide, pass2068_2391, by decide, by decide, pass2068_2393, by decide, by decide, pass2068_2398, by decide, by decide, pass2068_2412, by decide, by decide, pass2068_2449, rfl⟩
def src2069 : Request := ⟨⟨⟨1750,2442,527,21920⟩,161065121873920,975196209190⟩,3,2,1,257073,20⟩
private theorem pass2069_2390 : (Triangular src2069) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2069_2391 : (Triangular src2069) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2069_2393 : (Triangular src2069) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2069_2399 : (Triangular src2069) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2069_2415 : (Triangular src2069) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2069_2457 : (Triangular src2069) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2069 : Cover (Triangular src2069) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2069_2390, by decide, by decide, pass2069_2391, by decide, by decide, pass2069_2393, by decide, by decide, pass2069_2399, by decide, by decide, pass2069_2415, by decide, by decide, pass2069_2457, rfl⟩
def src2070 : Request := ⟨⟨⟨2100,2930,632,26671⟩,278060332482560,2019119590628⟩,6,2,1,257073,20⟩
private theorem pass2070_2390 : (Triangular src2070) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2070_2391 : (Triangular src2070) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2070_2393 : (Triangular src2070) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2070_2398 : (Triangular src2070) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2070_2412 : (Triangular src2070) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2070_2449 : (Triangular src2070) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2070 : Cover (Triangular src2070) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2070_2390, by decide, by decide, pass2070_2391, by decide, by decide, pass2070_2393, by decide, by decide, pass2070_2398, by decide, by decide, pass2070_2412, by decide, by decide, pass2070_2449, rfl⟩
def src2071 : Request := ⟨⟨⟨2600,3628,783,33149⟩,527755772952576,4745819470168⟩,10,2,1,257073,20⟩
private theorem pass2071_2390 : (Triangular src2071) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2071_2391 : (Triangular src2071) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2071_2393 : (Triangular src2071) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2071_2398 : (Triangular src2071) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2071_2412 : (Triangular src2071) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2071_2448 : (Triangular src2071) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2071 : Cover (Triangular src2071) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2071_2390, by decide, by decide, pass2071_2391, by decide, by decide, pass2071_2393, by decide, by decide, pass2071_2398, by decide, by decide, pass2071_2412, by decide, by decide, pass2071_2448, rfl⟩
def src2072 : Request := ⟨⟨⟨3950,5512,1189,50049⟩,1848744952463360,25255771038451⟩,20,2,1,257073,20⟩
private theorem pass2072_2390 : (Triangular src2072) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2072_2391 : (Triangular src2072) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2072_2393 : (Triangular src2072) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2072_2398 : (Triangular src2072) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2072_2411 : (Triangular src2072) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2072_2445 : (Triangular src2072) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2072_2534 : (Triangular src2072) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2072 : Cover (Triangular src2072) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2072_2390, by decide, by decide, pass2072_2391, by decide, by decide, pass2072_2393, by decide, by decide, pass2072_2398, by decide, by decide, pass2072_2411, by decide, by decide, pass2072_2445, by decide, by decide, pass2072_2534, rfl⟩
def src2073 : Request := ⟨⟨⟨4800,6698,1445,78274⟩,3317023033262080,55058665830093⟩,40,2,1,257073,20⟩
private theorem pass2073_2390 : (Triangular src2073) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2073_2391 : (Triangular src2073) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2073_2393 : (Triangular src2073) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2073_2398 : (Triangular src2073) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2073_2411 : (Triangular src2073) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2073_2445 : (Triangular src2073) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2073_2534 : (Triangular src2073) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2073 : Cover (Triangular src2073) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2073_2390, by decide, by decide, pass2073_2391, by decide, by decide, pass2073_2393, by decide, by decide, pass2073_2398, by decide, by decide, pass2073_2411, by decide, by decide, pass2073_2445, by decide, by decide, pass2073_2534, rfl⟩
def src2074 : Request := ⟨⟨⟨6900,9629,2077,85238⟩,9849424459857920,235044796335102⟩,40,2,1,257073,20⟩
private theorem pass2074_2390 : (Triangular src2074) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2074_2391 : (Triangular src2074) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2074_2393 : (Triangular src2074) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2074_2398 : (Triangular src2074) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2074_2411 : (Triangular src2074) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2074_2445 : (Triangular src2074) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2074_2533 : (Triangular src2074) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2074 : Cover (Triangular src2074) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2074_2390, by decide, by decide, pass2074_2391, by decide, by decide, pass2074_2393, by decide, by decide, pass2074_2398, by decide, by decide, pass2074_2411, by decide, by decide, pass2074_2445, by decide, by decide, pass2074_2533, rfl⟩
def src2075 : Request := ⟨⟨⟨6900,9628,2077,118434⟩,9849424459857920,234966243278304⟩,65,2,1,257073,20⟩
private theorem pass2075_2390 : (Triangular src2075) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2075_2391 : (Triangular src2075) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2075_2393 : (Triangular src2075) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2075_2398 : (Triangular src2075) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2075_2411 : (Triangular src2075) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2075_2445 : (Triangular src2075) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2075_2533 : (Triangular src2075) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2075 : Cover (Triangular src2075) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2075_2390, by decide, by decide, pass2075_2391, by decide, by decide, pass2075_2393, by decide, by decide, pass2075_2398, by decide, by decide, pass2075_2411, by decide, by decide, pass2075_2445, by decide, by decide, pass2075_2533, rfl⟩
def src2076 : Request := ⟨⟨⟨10000,13955,3010,125771⟩,29974681586237440,1036603432174989⟩,65,2,1,257073,20⟩
private theorem pass2076_2390 : (Triangular src2076) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2076_2391 : (Triangular src2076) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2076_2393 : (Triangular src2076) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2076_2398 : (Triangular src2076) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2076_2411 : (Triangular src2076) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2076_2445 : (Triangular src2076) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2076_2533 : (Triangular src2076) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2076 : Cover (Triangular src2076) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2076_2390, by decide, by decide, pass2076_2391, by decide, by decide, pass2076_2393, by decide, by decide, pass2076_2398, by decide, by decide, pass2076_2411, by decide, by decide, pass2076_2445, by decide, by decide, pass2076_2533, rfl⟩
def src2077 : Request := ⟨⟨⟨1750,2442,537,17151⟩,163381988556800,989573241440⟩,0,2,1,257073,21⟩
private theorem pass2077_2390 : (Triangular src2077) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2077_2391 : (Triangular src2077) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2077_2393 : (Triangular src2077) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2077_2398 : (Triangular src2077) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2077_2412 : (Triangular src2077) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2077_2449 : (Triangular src2077) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2077 : Cover (Triangular src2077) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2077_2390, by decide, by decide, pass2077_2391, by decide, by decide, pass2077_2393, by decide, by decide, pass2077_2398, by decide, by decide, pass2077_2412, by decide, by decide, pass2077_2449, rfl⟩
def src2078 : Request := ⟨⟨⟨1750,2442,527,18367⟩,161065121873920,975196209190⟩,1,2,1,257073,21⟩
private theorem pass2078_2390 : (Triangular src2078) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2078_2391 : (Triangular src2078) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2078_2393 : (Triangular src2078) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2078_2399 : (Triangular src2078) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2078_2415 : (Triangular src2078) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2078_2457 : (Triangular src2078) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2078 : Cover (Triangular src2078) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2078_2390, by decide, by decide, pass2078_2391, by decide, by decide, pass2078_2393, by decide, by decide, pass2078_2399, by decide, by decide, pass2078_2415, by decide, by decide, pass2078_2457, rfl⟩
def src2079 : Request := ⟨⟨⟨1750,2442,527,18995⟩,161065121873920,975196209190⟩,2,2,1,257073,21⟩
private theorem pass2079_2390 : (Triangular src2079) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2079_2391 : (Triangular src2079) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2079_2393 : (Triangular src2079) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2079_2399 : (Triangular src2079) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2079_2415 : (Triangular src2079) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2079_2457 : (Triangular src2079) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2079 : Cover (Triangular src2079) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2079_2390, by decide, by decide, pass2079_2391, by decide, by decide, pass2079_2393, by decide, by decide, pass2079_2399, by decide, by decide, pass2079_2415, by decide, by decide, pass2079_2457, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1752

-- Source: Research6969.PrefixRescueDataMiddle76
section Z6969Source1753
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle76
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,19⟩
  bank i := ![bank236 19562, bank245 22518, bank252 26836, bank252 27758, bank270 34973, bank303 43957, bank347 79307, bank373 133661, bank386 140635, bank359 136716, bank386 140635] i
  reserve i := ![0, 1, 3, 4, 8, 13, 32, 65, 65, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 19

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 19562
    · exact rank245 22518
    · exact rank252 26836
    · exact rank252 27758
    · exact rank270 34973
    · exact rank303 43957
    · exact rank347 79307
    · exact rank373 133661
    · exact rank386 140635
    · exact rank359 136716
    · exact rank386 140635
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2056⟩
    · exact ⟨_, cover2057⟩
    · exact ⟨_, cover2058⟩
    · exact ⟨_, cover2059⟩
    · exact ⟨_, cover2060⟩
    · exact ⟨_, cover2061⟩
    · exact ⟨_, cover2062⟩
    · exact ⟨_, cover2064⟩
    · exact ⟨_, cover2065⟩
    · exact ⟨_, cover2063⟩
    · exact ⟨_, cover2065⟩

def price : EarlyPrice := ⟨2, 19, 10, 85/100, 80/100, ![1041346342905, 135852073940, 22287855030, 1173066230], 3132874932911886⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 176179/66, 228182/33, 230869/6] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle76
end Z6969Source1753

-- Source: Research6969.PrefixMiddleSaved76
section Z6969Source1754
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved76
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle76.price Lower6960.Prefix6969RescueData.Middle76.price :=
  ⟨336, 3869, 177, 2669, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle76.plan Lower6960.Prefix6969RescueData.Middle76.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 19 19 :=
  ⟨Lower6960.Prefix6969MainCases.Middle76.plan, Lower6960.Prefix6969MainCases.Middle76.price, Lower6960.Prefix6969MainCases.Middle76.valid, Lower6960.Prefix6969MainCases.Middle76.priced, Lower6960.Prefix6969MainCases.Middle76.sources,
   Lower6960.Prefix6969RescueData.Middle76.plan, Lower6960.Prefix6969RescueData.Middle76.price, Lower6960.Prefix6969RescueData.Middle76.sources, Lower6960.Prefix6969RescueData.Middle76.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved76
end Z6969Source1754

-- Source: Research6969.PrefixMainDataMiddle77
section Z6969Source1755
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle77
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank186 19684, bank175 25973, bank169 29097] i
  head := src2762
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15027, 125990, 584736, 2139818],
    ![12303, 98747, 446479, 1590545],
    ![53398/9, 429292/9, 446479, 1590545],
    ![29433/8, 232387/8, 2103940/9, 820248],
    ![63824/25, 502296/25, 313709/2, 2253001/4],
    ![72196/49, 570054/49, 2569354/25, 9012212/25],
    ![40539/50, 336161/50, 71355, 1134225/4],
    ![95180/121, 717240/121, 3226184/49, 10799932/49],
    ![95180/121, 717240/121, 116003/2, 870489/4],
    ![63754/121, 751724/147, 770661/16, 10363518/49],
    ![63754/121, 751724/147, 770661/16, 588896/3],
    ![63754/121, 605203/121, 770661/16, 9114361/64],
    ![1355575/3362, 605203/121, 770661/16, 9114361/64],
    ![1355575/3362, 7195568/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 1756100/441, 4332756/121, 14470416/121],
    ![481425/1369, 1756100/441, 4332756/121, 14470416/121],
    ![929061/2738, 1756100/441, 4332756/121, 14470416/121],
    ![459151/1369, 1756100/441, 4332756/121, 14470416/121]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 20 257073 := by
  refine ⟨?_, rank154 5258, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2762⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free49_1
    · exact free58_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free126_1
    · exact free153_1
    · exact free199_1
    · exact free186_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [254263066, 330421184, 330304637, 330695863, 329380663, 331260180, 329470694, 148007347, 148015753, 148548054, 148257042, 70913668, 71985065, 90016352, 104062727, 102397073, 172034813, 223336812], [1425852, 1042051, 1042370, 1041297, 1044905, 1039749, 1044658, 2602833, 2602693, 2593833, 2598677, 5659636, 5574392, 4419302, 3788238, 3857670, 2210129, 1669229],
  ![118551646545840, 1619498228388, 204721427470, 4590627300], 138907642667542201⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 1756100/441, 4332756/121, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle77
end Z6969Source1755

-- Source: Research6969.PrefixRescueDataMiddle77
section Z6969Source1756
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle77
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,20⟩
  bank i := ![bank236 17554, bank236 18436, bank246 20387, bank245 21920, bank252 26671, bank270 33149, bank315 50049, bank361 85238, bank332 78274, bank359 118434, bank386 125771] i
  reserve i := ![0, 1, 2, 3, 6, 10, 20, 40, 40, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 20

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 17554
    · exact rank236 18436
    · exact rank246 20387
    · exact rank245 21920
    · exact rank252 26671
    · exact rank270 33149
    · exact rank315 50049
    · exact rank361 85238
    · exact rank332 78274
    · exact rank359 118434
    · exact rank386 125771
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2066⟩
    · exact ⟨_, cover2067⟩
    · exact ⟨_, cover2068⟩
    · exact ⟨_, cover2069⟩
    · exact ⟨_, cover2070⟩
    · exact ⟨_, cover2071⟩
    · exact ⟨_, cover2072⟩
    · exact ⟨_, cover2074⟩
    · exact ⟨_, cover2073⟩
    · exact ⟨_, cover2075⟩
    · exact ⟨_, cover2076⟩

def price : EarlyPrice := ⟨2, 20, 10, 85/100, 80/100, ![980299169178, 134324661943, 23460897180, 1173066230], 2781482814837383⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 79987/33, 214714/33, 394780/11] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle77
end Z6969Source1756

-- Source: Research6969.PrefixMiddleSaved77
section Z6969Source1757
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved77
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle77.price Lower6960.Prefix6969RescueData.Middle77.price :=
  ⟨335, 3982, 177, 2423, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle77.plan Lower6960.Prefix6969RescueData.Middle77.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 20 20 :=
  ⟨Lower6960.Prefix6969MainCases.Middle77.plan, Lower6960.Prefix6969MainCases.Middle77.price, Lower6960.Prefix6969MainCases.Middle77.valid, Lower6960.Prefix6969MainCases.Middle77.priced, Lower6960.Prefix6969MainCases.Middle77.sources,
   Lower6960.Prefix6969RescueData.Middle77.plan, Lower6960.Prefix6969RescueData.Middle77.price, Lower6960.Prefix6969RescueData.Middle77.sources, Lower6960.Prefix6969RescueData.Middle77.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved77
end Z6969Source1757

-- Source: Research6969.PrefixMainDataMiddle78
section Z6969Source1758
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle78
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank162 16965, bank178 23472, bank170 28384, bank213 8827] i
  head := src2763
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15063, 125705, 584415, 2127671],
    ![12303, 98108, 887207/2, 3138135/2],
    ![53398/9, 426523/9, 887207/2, 3138135/2],
    ![29433/8, 461721/16, 696722/3, 809172],
    ![63824/25, 498959/25, 313709/2, 2253001/4],
    ![72196/49, 566291/49, 2552527/25, 8890518/25],
    ![40539/50, 668133/100, 71355, 1134225/4],
    ![95180/121, 712270/121, 3204032/49, 1522014/7],
    ![95180/121, 712270/121, 116003/2, 1522014/7],
    ![63754/121, 249202/49, 770661/16, 1460511/7],
    ![63754/121, 249202/49, 770661/16, 193648],
    ![63754/121, 600659/121, 770661/16, 9114361/64],
    ![1355575/3362, 600659/121, 770661/16, 9114361/64],
    ![1355575/3362, 7168956/1681, 8051793/196, 6610041/49],
    ![1355575/3362, 1744030/441, 4332756/121, 14470416/121],
    ![483776/1323, 1744030/441, 4332756/121, 14470416/121],
    ![939225/2738, 1744030/441, 4332756/121, 14470416/121],
    ![920087/2738, 1744030/441, 4332756/121, 14470416/121],
    ![920087/2738, 5222126/1369, 1816675/52, 1896447/16]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 21 257073 := by
  refine ⟨?_, rank154 5187, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2763⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free49_1
    · exact free58_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free126_1
    · exact free161_1
    · exact free199_1
    · exact free162_1
    · exact free178_1
    · exact free170_1
    · exact free213_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [253156741, 327835046, 327884130, 328483225, 327566228, 328618384, 327927736, 150492029, 150340294, 150484178, 150382262, 72396804, 72493904, 87413784, 87490355, 100000000, 150617209, 101901537, 233302171], [1431518, 1049146, 1049011, 1047367, 1050441, 1046997, 1048892, 2561477, 2564003, 2561608, 2563304, 5541633, 5533907, 4550684, 4546819, 3958949, 2559394, 3878607, 1587207],
  ![123841458410220, 1608685549304, 209971953900, 4711149310], 139761071731354662⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 5222126/1369, 1816675/52, 1896447/16] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle78
end Z6969Source1758

-- Source: Research6969.PhysicalChecks130
section Z6969Source1759
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2080 : Request := ⟨⟨⟨1750,2442,527,20453⟩,161065121873920,975196209190⟩,4,2,1,257073,21⟩
private theorem pass2080_2390 : (Triangular src2080) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2080_2391 : (Triangular src2080) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2080_2393 : (Triangular src2080) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2080_2399 : (Triangular src2080) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2080_2415 : (Triangular src2080) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2080_2457 : (Triangular src2080) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2080 : Cover (Triangular src2080) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2080_2390, by decide, by decide, pass2080_2391, by decide, by decide, pass2080_2393, by decide, by decide, pass2080_2399, by decide, by decide, pass2080_2415, by decide, by decide, pass2080_2457, rfl⟩
def src2081 : Request := ⟨⟨⟨2100,2930,632,22540⟩,278060332482560,2019119590628⟩,4,2,1,257073,21⟩
private theorem pass2081_2390 : (Triangular src2081) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2081_2391 : (Triangular src2081) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2081_2393 : (Triangular src2081) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2081_2398 : (Triangular src2081) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2081_2412 : (Triangular src2081) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2081_2449 : (Triangular src2081) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2081 : Cover (Triangular src2081) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2081_2390, by decide, by decide, pass2081_2391, by decide, by decide, pass2081_2393, by decide, by decide, pass2081_2398, by decide, by decide, pass2081_2412, by decide, by decide, pass2081_2449, rfl⟩
def src2082 : Request := ⟨⟨⟨2600,3628,798,27226⟩,535425056505856,4816500515660⟩,8,2,1,257073,21⟩
private theorem pass2082_2390 : (Triangular src2082) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2082_2391 : (Triangular src2082) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2082_2393 : (Triangular src2082) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2082_2398 : (Triangular src2082) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2082_2411 : (Triangular src2082) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2082_2445 : (Triangular src2082) 2445 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2082 : Cover (Triangular src2082) 2534 2390 [2390,2392,2397,2410,2444,2534] := by
  exact ⟨by decide, by decide, pass2082_2390, by decide, by decide, pass2082_2391, by decide, by decide, pass2082_2393, by decide, by decide, pass2082_2398, by decide, by decide, pass2082_2411, by decide, by decide, pass2082_2445, rfl⟩
def src2083 : Request := ⟨⟨⟨3200,4465,963,37728⟩,983050615259136,10877088344236⟩,16,2,1,257073,21⟩
private theorem pass2083_2390 : (Triangular src2083) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2083_2391 : (Triangular src2083) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2083_2393 : (Triangular src2083) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2083_2398 : (Triangular src2083) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2083_2411 : (Triangular src2083) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2083_2446 : (Triangular src2083) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2083 : Cover (Triangular src2083) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2083_2390, by decide, by decide, pass2083_2391, by decide, by decide, pass2083_2393, by decide, by decide, pass2083_2398, by decide, by decide, pass2083_2411, by decide, by decide, pass2083_2446, rfl⟩
def src2084 : Request := ⟨⟨⟨5700,7954,1750,61233⟩,5637370734182400,111160708353364⟩,32,2,1,257073,21⟩
private theorem pass2084_2390 : (Triangular src2084) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2084_2391 : (Triangular src2084) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2084_2393 : (Triangular src2084) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2084_2398 : (Triangular src2084) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2084_2411 : (Triangular src2084) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2084_2445 : (Triangular src2084) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2084_2532 : (Triangular src2084) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2084 : Cover (Triangular src2084) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2084_2390, by decide, by decide, pass2084_2391, by decide, by decide, pass2084_2393, by decide, by decide, pass2084_2398, by decide, by decide, pass2084_2411, by decide, by decide, pass2084_2445, by decide, by decide, pass2084_2532, rfl⟩
def src2085 : Request := ⟨⟨⟨4800,6698,1445,68286⟩,3317023033262080,55058665830093⟩,40,2,1,257073,21⟩
private theorem pass2085_2390 : (Triangular src2085) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2085_2391 : (Triangular src2085) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2085_2393 : (Triangular src2085) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2085_2398 : (Triangular src2085) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2085_2411 : (Triangular src2085) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2085_2445 : (Triangular src2085) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2085_2534 : (Triangular src2085) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2085 : Cover (Triangular src2085) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2085_2390, by decide, by decide, pass2085_2391, by decide, by decide, pass2085_2393, by decide, by decide, pass2085_2398, by decide, by decide, pass2085_2411, by decide, by decide, pass2085_2445, by decide, by decide, pass2085_2534, rfl⟩
def src2086 : Request := ⟨⟨⟨6900,9628,2077,102712⟩,9849424459857920,234966243278304⟩,65,2,1,257073,21⟩
private theorem pass2086_2390 : (Triangular src2086) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2086_2391 : (Triangular src2086) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2086_2393 : (Triangular src2086) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2086_2398 : (Triangular src2086) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2086_2411 : (Triangular src2086) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2086_2445 : (Triangular src2086) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2086_2533 : (Triangular src2086) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2086 : Cover (Triangular src2086) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2086_2390, by decide, by decide, pass2086_2391, by decide, by decide, pass2086_2393, by decide, by decide, pass2086_2398, by decide, by decide, pass2086_2411, by decide, by decide, pass2086_2445, by decide, by decide, pass2086_2533, rfl⟩
def src2087 : Request := ⟨⟨⟨10000,13955,3070,108301⟩,30428373265940480,1052683166434338⟩,65,2,1,257073,21⟩
private theorem pass2087_2390 : (Triangular src2087) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2087_2391 : (Triangular src2087) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2087_2393 : (Triangular src2087) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2087_2398 : (Triangular src2087) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2087_2411 : (Triangular src2087) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2087_2444 : (Triangular src2087) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2087_2529 : (Triangular src2087) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2087 : Cover (Triangular src2087) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2087_2390, by decide, by decide, pass2087_2391, by decide, by decide, pass2087_2393, by decide, by decide, pass2087_2398, by decide, by decide, pass2087_2411, by decide, by decide, pass2087_2444, by decide, by decide, pass2087_2529, rfl⟩
def src2088 : Request := ⟨⟨⟨1200,1674,361,12912⟩,51955677528064,215563369662⟩,0,2,1,257073,22⟩
private theorem pass2088_2390 : (Triangular src2088) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2088_2391 : (Triangular src2088) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2088_2393 : (Triangular src2088) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2088_2399 : (Triangular src2088) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2088_2415 : (Triangular src2088) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2088_2459 : (Triangular src2088) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2088 : Cover (Triangular src2088) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2088_2390, by decide, by decide, pass2088_2391, by decide, by decide, pass2088_2393, by decide, by decide, pass2088_2399, by decide, by decide, pass2088_2415, by decide, by decide, pass2088_2459, rfl⟩
def src2089 : Request := ⟨⟨⟨1450,2023,445,14275⟩,92998964346880,466511127281⟩,1,2,1,257073,22⟩
private theorem pass2089_2390 : (Triangular src2089) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2089_2391 : (Triangular src2089) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2089_2393 : (Triangular src2089) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2089_2399 : (Triangular src2089) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2089_2415 : (Triangular src2089) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2089_2457 : (Triangular src2089) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2089 : Cover (Triangular src2089) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2089_2390, by decide, by decide, pass2089_2391, by decide, by decide, pass2089_2393, by decide, by decide, pass2089_2399, by decide, by decide, pass2089_2415, by decide, by decide, pass2089_2457, rfl⟩
def src2090 : Request := ⟨⟨⟨1450,2023,445,14867⟩,92998964346880,466511127281⟩,2,2,1,257073,22⟩
private theorem pass2090_2390 : (Triangular src2090) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2090_2391 : (Triangular src2090) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2090_2393 : (Triangular src2090) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2090_2399 : (Triangular src2090) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2090_2415 : (Triangular src2090) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2090_2457 : (Triangular src2090) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2090 : Cover (Triangular src2090) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2090_2390, by decide, by decide, pass2090_2391, by decide, by decide, pass2090_2393, by decide, by decide, pass2090_2399, by decide, by decide, pass2090_2415, by decide, by decide, pass2090_2457, rfl⟩
def src2091 : Request := ⟨⟨⟨1750,2442,537,17665⟩,163381988556800,989573241440⟩,4,2,1,257073,22⟩
private theorem pass2091_2390 : (Triangular src2091) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2091_2391 : (Triangular src2091) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2091_2393 : (Triangular src2091) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2091_2398 : (Triangular src2091) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2091_2412 : (Triangular src2091) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2091_2449 : (Triangular src2091) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2091 : Cover (Triangular src2091) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2091_2390, by decide, by decide, pass2091_2391, by decide, by decide, pass2091_2393, by decide, by decide, pass2091_2398, by decide, by decide, pass2091_2412, by decide, by decide, pass2091_2449, rfl⟩
def src2092 : Request := ⟨⟨⟨2100,2930,632,21621⟩,278060332482560,2019119590628⟩,6,2,1,257073,22⟩
private theorem pass2092_2390 : (Triangular src2092) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2092_2391 : (Triangular src2092) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2092_2393 : (Triangular src2092) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2092_2398 : (Triangular src2092) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2092_2412 : (Triangular src2092) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2092_2449 : (Triangular src2092) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2092 : Cover (Triangular src2092) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2092_2390, by decide, by decide, pass2092_2391, by decide, by decide, pass2092_2393, by decide, by decide, pass2092_2398, by decide, by decide, pass2092_2412, by decide, by decide, pass2092_2449, rfl⟩
def src2093 : Request := ⟨⟨⟨2600,3628,783,26844⟩,527755772952576,4745819470168⟩,10,2,1,257073,22⟩
private theorem pass2093_2390 : (Triangular src2093) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2093_2391 : (Triangular src2093) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2093_2393 : (Triangular src2093) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2093_2398 : (Triangular src2093) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2093_2412 : (Triangular src2093) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2093_2449 : (Triangular src2093) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2093 : Cover (Triangular src2093) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2093_2390, by decide, by decide, pass2093_2391, by decide, by decide, pass2093_2393, by decide, by decide, pass2093_2398, by decide, by decide, pass2093_2412, by decide, by decide, pass2093_2449, rfl⟩
def src2094 : Request := ⟨⟨⟨3950,5512,1213,38818⟩,1877062482395136,25652240151764⟩,20,2,1,257073,22⟩
private theorem pass2094_2390 : (Triangular src2094) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2094_2391 : (Triangular src2094) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2094_2393 : (Triangular src2094) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2094_2398 : (Triangular src2094) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2094_2411 : (Triangular src2094) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2094_2445 : (Triangular src2094) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2094_2533 : (Triangular src2094) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2094 : Cover (Triangular src2094) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2094_2390, by decide, by decide, pass2094_2391, by decide, by decide, pass2094_2393, by decide, by decide, pass2094_2398, by decide, by decide, pass2094_2411, by decide, by decide, pass2094_2445, by decide, by decide, pass2094_2533, rfl⟩
def src2095 : Request := ⟨⟨⟨6900,9628,2077,75848⟩,9849424459857920,234966243278304⟩,50,2,1,257073,22⟩
private theorem pass2095_2390 : (Triangular src2095) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2095_2391 : (Triangular src2095) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2095_2393 : (Triangular src2095) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2095_2398 : (Triangular src2095) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2095_2411 : (Triangular src2095) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2095_2445 : (Triangular src2095) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2095_2533 : (Triangular src2095) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2095 : Cover (Triangular src2095) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2095_2390, by decide, by decide, pass2095_2391, by decide, by decide, pass2095_2393, by decide, by decide, pass2095_2398, by decide, by decide, pass2095_2411, by decide, by decide, pass2095_2445, by decide, by decide, pass2095_2533, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1759

end Merged_Z6969Pack0725

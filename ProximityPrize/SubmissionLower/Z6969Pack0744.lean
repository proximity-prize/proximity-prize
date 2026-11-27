import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0743
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0744
section Merged_Z6969Pack0744

-- Source: Research6969.PrefixRescueDataMiddle46
section Z6969Source1976
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle46
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,21⟩
  bank i := ![bank221 9475, bank221 9858, bank221 10284, bank228 11351, bank227 12179, bank237 14641, bank271 27515, bank346 59334, bank355 94628, bank382 102836, bank367 124806] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385610
  seedFloor := 21

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 9475
    · exact rank221 9858
    · exact rank221 10284
    · exact rank228 11351
    · exact rank227 12179
    · exact rank237 14641
    · exact rank271 27515
    · exact rank346 59334
    · exact rank355 94628
    · exact rank382 102836
    · exact rank367 124806
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2514⟩
    · exact ⟨_, cover2515⟩
    · exact ⟨_, cover2516⟩
    · exact ⟨_, cover2517⟩
    · exact ⟨_, cover2518⟩
    · exact ⟨_, cover2519⟩
    · exact ⟨_, cover2520⟩
    · exact ⟨_, cover2521⟩
    · exact ⟨_, cover2522⟩
    · exact ⟨_, cover2523⟩
    · exact ⟨_, cover2524⟩

def price : EarlyPrice := ⟨3, 21, 10, 80/100, 70/100, ![1021416547404, 171597876588, 24633942340, 2346111390], 1572986129637647⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 88632/73, 617577/146, 662396/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle46
end Z6969Source1976

-- Source: Research6969.PrefixMiddleSaved46
section Z6969Source1977
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved46
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle46.price Lower6960.Prefix6969RescueData.Middle46.price :=
  ⟨336, 3732, 113, 1214, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle46.plan Lower6960.Prefix6969RescueData.Middle46.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 21 21 :=
  ⟨Lower6960.Prefix6969MainCases.Middle46.plan, Lower6960.Prefix6969MainCases.Middle46.price, Lower6960.Prefix6969MainCases.Middle46.valid, Lower6960.Prefix6969MainCases.Middle46.priced, Lower6960.Prefix6969MainCases.Middle46.sources,
   Lower6960.Prefix6969RescueData.Middle46.plan, Lower6960.Prefix6969RescueData.Middle46.price, Lower6960.Prefix6969RescueData.Middle46.sources, Lower6960.Prefix6969RescueData.Middle46.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved46
end Z6969Source1977

-- Source: Research6969.PhysicalChecks184
section Z6969Source1978
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2944 : Request := ⟨⟨⟨556,772,170,4897⟩,5255817068544,9968090926⟩,10,4,2,514146,23⟩
private theorem pass2944_2390 : (Triangular src2944) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2944_2391 : (Triangular src2944) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2944_2394 : (Triangular src2944) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2944_2402 : (Triangular src2944) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2944_2426 : (Triangular src2944) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2944_2496 : (Triangular src2944) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2944 : Cover (Triangular src2944) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2944_2390, by decide, by decide, pass2944_2391, by decide, by decide, pass2944_2394, by decide, by decide, pass2944_2402, by decide, by decide, pass2944_2426, by decide, by decide, pass2944_2496, rfl⟩
def src2945 : Request := ⟨⟨⟨556,772,170,4838⟩,5255817068544,9968090926⟩,10,4,2,514146,24⟩
private theorem pass2945_2390 : (Triangular src2945) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2945_2391 : (Triangular src2945) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2945_2394 : (Triangular src2945) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2945_2402 : (Triangular src2945) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2945_2426 : (Triangular src2945) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2945_2496 : (Triangular src2945) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2945 : Cover (Triangular src2945) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2945_2390, by decide, by decide, pass2945_2391, by decide, by decide, pass2945_2394, by decide, by decide, pass2945_2402, by decide, by decide, pass2945_2426, by decide, by decide, pass2945_2496, rfl⟩
def src2946 : Request := ⟨⟨⟨556,772,170,4780⟩,5255817068544,9968090926⟩,10,4,2,514146,25⟩
private theorem pass2946_2390 : (Triangular src2946) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2946_2391 : (Triangular src2946) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2946_2393 : (Triangular src2946) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2946_2399 : (Triangular src2946) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2946_2417 : (Triangular src2946) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2946_2469 : (Triangular src2946) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2946 : Cover (Triangular src2946) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2946_2390, by decide, by decide, pass2946_2391, by decide, by decide, pass2946_2393, by decide, by decide, pass2946_2399, by decide, by decide, pass2946_2417, by decide, by decide, pass2946_2469, rfl⟩
def src2947 : Request := ⟨⟨⟨556,772,170,4724⟩,5255817068544,9968090926⟩,10,4,2,514146,26⟩
private theorem pass2947_2390 : (Triangular src2947) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2947_2391 : (Triangular src2947) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2947_2394 : (Triangular src2947) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2947_2402 : (Triangular src2947) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2947_2426 : (Triangular src2947) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2947_2496 : (Triangular src2947) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2947 : Cover (Triangular src2947) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2947_2390, by decide, by decide, pass2947_2391, by decide, by decide, pass2947_2394, by decide, by decide, pass2947_2402, by decide, by decide, pass2947_2426, by decide, by decide, pass2947_2496, rfl⟩
def src2948 : Request := ⟨⟨⟨556,772,170,4668⟩,5255817068544,9968090926⟩,10,4,2,514146,27⟩
private theorem pass2948_2390 : (Triangular src2948) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2948_2391 : (Triangular src2948) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2948_2393 : (Triangular src2948) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2948_2399 : (Triangular src2948) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2948_2417 : (Triangular src2948) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2948_2469 : (Triangular src2948) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2948 : Cover (Triangular src2948) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2948_2390, by decide, by decide, pass2948_2391, by decide, by decide, pass2948_2393, by decide, by decide, pass2948_2399, by decide, by decide, pass2948_2417, by decide, by decide, pass2948_2469, rfl⟩
def src2949 : Request := ⟨⟨⟨556,772,170,4614⟩,5255817068544,9968090926⟩,10,4,2,514146,28⟩
private theorem pass2949_2390 : (Triangular src2949) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2949_2391 : (Triangular src2949) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2949_2394 : (Triangular src2949) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2949_2402 : (Triangular src2949) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2949_2426 : (Triangular src2949) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2949_2496 : (Triangular src2949) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2949 : Cover (Triangular src2949) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2949_2390, by decide, by decide, pass2949_2391, by decide, by decide, pass2949_2394, by decide, by decide, pass2949_2402, by decide, by decide, pass2949_2426, by decide, by decide, pass2949_2496, rfl⟩
def src2950 : Request := ⟨⟨⟨556,772,170,4560⟩,5255817068544,9968090926⟩,10,4,2,514146,29⟩
private theorem pass2950_2390 : (Triangular src2950) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2950_2391 : (Triangular src2950) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2950_2393 : (Triangular src2950) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2950_2399 : (Triangular src2950) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2950_2417 : (Triangular src2950) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2950_2469 : (Triangular src2950) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2950 : Cover (Triangular src2950) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2950_2390, by decide, by decide, pass2950_2391, by decide, by decide, pass2950_2393, by decide, by decide, pass2950_2399, by decide, by decide, pass2950_2417, by decide, by decide, pass2950_2469, rfl⟩
def src2951 : Request := ⟨⟨⟨556,772,170,4508⟩,5255817068544,9968090926⟩,10,4,2,514146,30⟩
private theorem pass2951_2390 : (Triangular src2951) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2951_2391 : (Triangular src2951) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2951_2394 : (Triangular src2951) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2951_2402 : (Triangular src2951) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2951_2426 : (Triangular src2951) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2951_2496 : (Triangular src2951) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2951 : Cover (Triangular src2951) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2951_2390, by decide, by decide, pass2951_2391, by decide, by decide, pass2951_2394, by decide, by decide, pass2951_2402, by decide, by decide, pass2951_2426, by decide, by decide, pass2951_2496, rfl⟩
def src2952 : Request := ⟨⟨⟨556,772,170,4457⟩,5255817068544,9968090926⟩,10,4,2,514146,31⟩
private theorem pass2952_2390 : (Triangular src2952) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2952_2391 : (Triangular src2952) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2952_2394 : (Triangular src2952) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2952_2402 : (Triangular src2952) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2952_2426 : (Triangular src2952) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2952_2496 : (Triangular src2952) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2952 : Cover (Triangular src2952) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2952_2390, by decide, by decide, pass2952_2391, by decide, by decide, pass2952_2394, by decide, by decide, pass2952_2402, by decide, by decide, pass2952_2426, by decide, by decide, pass2952_2496, rfl⟩
def src2953 : Request := ⟨⟨⟨556,772,170,4407⟩,5255817068544,9968090926⟩,10,4,2,514146,32⟩
private theorem pass2953_2390 : (Triangular src2953) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2953_2391 : (Triangular src2953) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2953_2394 : (Triangular src2953) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2953_2402 : (Triangular src2953) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2953_2426 : (Triangular src2953) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2953_2496 : (Triangular src2953) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2953 : Cover (Triangular src2953) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2953_2390, by decide, by decide, pass2953_2391, by decide, by decide, pass2953_2394, by decide, by decide, pass2953_2402, by decide, by decide, pass2953_2426, by decide, by decide, pass2953_2496, rfl⟩
def src2954 : Request := ⟨⟨⟨556,772,170,4358⟩,5255817068544,9968090926⟩,10,4,2,514146,33⟩
private theorem pass2954_2390 : (Triangular src2954) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2954_2391 : (Triangular src2954) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2954_2393 : (Triangular src2954) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2954_2399 : (Triangular src2954) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2954_2417 : (Triangular src2954) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2954_2469 : (Triangular src2954) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2954 : Cover (Triangular src2954) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2954_2390, by decide, by decide, pass2954_2391, by decide, by decide, pass2954_2393, by decide, by decide, pass2954_2399, by decide, by decide, pass2954_2417, by decide, by decide, pass2954_2469, rfl⟩
def src2955 : Request := ⟨⟨⟨556,772,170,4311⟩,5255817068544,9968090926⟩,10,4,2,514146,34⟩
private theorem pass2955_2390 : (Triangular src2955) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2955_2391 : (Triangular src2955) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2955_2394 : (Triangular src2955) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2955_2402 : (Triangular src2955) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2955_2426 : (Triangular src2955) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2955_2496 : (Triangular src2955) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2955 : Cover (Triangular src2955) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2955_2390, by decide, by decide, pass2955_2391, by decide, by decide, pass2955_2394, by decide, by decide, pass2955_2402, by decide, by decide, pass2955_2426, by decide, by decide, pass2955_2496, rfl⟩
def src2956 : Request := ⟨⟨⟨556,772,170,4265⟩,5255817068544,9968090926⟩,10,4,2,514146,35⟩
private theorem pass2956_2390 : (Triangular src2956) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2956_2391 : (Triangular src2956) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2956_2394 : (Triangular src2956) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2956_2402 : (Triangular src2956) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2956_2426 : (Triangular src2956) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2956_2496 : (Triangular src2956) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2956 : Cover (Triangular src2956) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2956_2390, by decide, by decide, pass2956_2391, by decide, by decide, pass2956_2394, by decide, by decide, pass2956_2402, by decide, by decide, pass2956_2426, by decide, by decide, pass2956_2496, rfl⟩
def src2957 : Request := ⟨⟨⟨556,772,170,4220⟩,5255817068544,9968090926⟩,10,4,2,514146,36⟩
private theorem pass2957_2390 : (Triangular src2957) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2957_2391 : (Triangular src2957) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2957_2394 : (Triangular src2957) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2957_2402 : (Triangular src2957) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2957_2426 : (Triangular src2957) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2957_2496 : (Triangular src2957) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2957 : Cover (Triangular src2957) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2957_2390, by decide, by decide, pass2957_2391, by decide, by decide, pass2957_2394, by decide, by decide, pass2957_2402, by decide, by decide, pass2957_2426, by decide, by decide, pass2957_2496, rfl⟩
def src2958 : Request := ⟨⟨⟨556,772,170,4176⟩,5255817068544,9968090926⟩,10,4,2,514146,37⟩
private theorem pass2958_2390 : (Triangular src2958) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2958_2391 : (Triangular src2958) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2958_2394 : (Triangular src2958) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2958_2402 : (Triangular src2958) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2958_2426 : (Triangular src2958) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2958_2496 : (Triangular src2958) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2958 : Cover (Triangular src2958) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2958_2390, by decide, by decide, pass2958_2391, by decide, by decide, pass2958_2394, by decide, by decide, pass2958_2402, by decide, by decide, pass2958_2426, by decide, by decide, pass2958_2496, rfl⟩
def src2959 : Request := ⟨⟨⟨556,772,170,4133⟩,5255817068544,9968090926⟩,10,4,2,514146,38⟩
private theorem pass2959_2390 : (Triangular src2959) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2959_2391 : (Triangular src2959) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2959_2393 : (Triangular src2959) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2959_2399 : (Triangular src2959) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2959_2417 : (Triangular src2959) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2959_2469 : (Triangular src2959) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2959 : Cover (Triangular src2959) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2959_2390, by decide, by decide, pass2959_2391, by decide, by decide, pass2959_2393, by decide, by decide, pass2959_2399, by decide, by decide, pass2959_2417, by decide, by decide, pass2959_2469, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1978

-- Source: Research6969.PrefixMainDataMiddle47
section Z6969Source1979
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle47
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 16, 23, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank65 2772, bank95 2576, bank92 3992, bank137 3019, bank126 11206, bank149 5119, bank199 7608, bank180 21819, bank212 8810, bank170 28384] i
  head := src2944
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15294, 124706, 580820, 2055864],
    ![25417/2, 382299/4, 433993, 5793151/4],
    ![54680/9, 416030/9, 433993, 5793151/4],
    ![29433/8, 449251/16, 2033906/9, 763932],
    ![63052/25, 482472/25, 157352, 2289169/4],
    ![5710/3, 258425/18, 1170961/8, 489700],
    ![18775/16, 583495/64, 304304/3, 9049656/25],
    ![89110/121, 683635/121, 442678/7, 1503379/7],
    ![89110/121, 683635/121, 442678/7, 1503379/7],
    ![89110/121, 683635/121, 558992/9, 1658944/9],
    ![21715/32, 683635/121, 15562602/289, 1658944/9],
    ![21715/32, 582099/121, 2560979/49, 9114361/64],
    ![1355575/3362, 582099/121, 2560979/49, 9114361/64],
    ![1355575/3362, 1697823/400, 3844369/98, 26204161/196],
    ![1355575/3362, 564910/147, 34353177/968, 13971141/121],
    ![25627/74, 564910/147, 34353177/968, 13971141/121],
    ![25627/74, 20321973/5476, 91314965/2704, 19404025/169],
    ![920087/2738, 20321973/5476, 91314965/2704, 19404025/169]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 22 385610 := by
  refine ⟨?_, rank154 4897, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2944⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free35_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free95_1
    · exact free92_1
    · exact free137_1
    · exact free126_1
    · exact free149_1
    · exact free199_1
    · exact free180_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [248707130, 321350307, 321600264, 322182507, 321551057, 321074936, 321472927, 161704338, 161777745, 103682379, 78611255, 74212960, 55022347, 84235857, 97247799, 97825452, 147928297, 220959132], [1460413, 1082275, 1080995, 1078013, 1081247, 1083685, 1081647, 2374856, 2373634, 3803364, 5087323, 5397133, 7349144, 4735594, 4075232, 4050826, 2604149, 1688799],
  ![117289526448240, 1622078074668, 198863218800, 4997417920], 134128113104245364⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 20321973/5476, 91314965/2704, 19404025/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle47
end Z6969Source1979

-- Source: Research6969.PhysicalChecks158
section Z6969Source1980
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2528 : Request := ⟨⟨⟨1200,1674,368,10680⟩,52718727069696,218807905514⟩,3,3,1,385610,22⟩
private theorem pass2528_2390 : (Triangular src2528) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2528_2391 : (Triangular src2528) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2528_2393 : (Triangular src2528) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2528_2399 : (Triangular src2528) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2528_2415 : (Triangular src2528) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2528_2458 : (Triangular src2528) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2528 : Cover (Triangular src2528) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2528_2390, by decide, by decide, pass2528_2391, by decide, by decide, pass2528_2393, by decide, by decide, pass2528_2399, by decide, by decide, pass2528_2415, by decide, by decide, pass2528_2458, rfl⟩
def src2529 : Request := ⟨⟨⟨1200,1674,368,11023⟩,52718727069696,218807905514⟩,4,3,1,385610,22⟩
private theorem pass2529_2390 : (Triangular src2529) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2529_2391 : (Triangular src2529) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2529_2393 : (Triangular src2529) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2529_2399 : (Triangular src2529) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2529_2415 : (Triangular src2529) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2529_2458 : (Triangular src2529) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2529 : Cover (Triangular src2529) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2529_2390, by decide, by decide, pass2529_2391, by decide, by decide, pass2529_2393, by decide, by decide, pass2529_2399, by decide, by decide, pass2529_2415, by decide, by decide, pass2529_2458, rfl⟩
def src2530 : Request := ⟨⟨⟨1450,2023,445,13715⟩,92998964346880,466511127281⟩,8,3,1,385610,22⟩
private theorem pass2530_2390 : (Triangular src2530) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2530_2391 : (Triangular src2530) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2530_2393 : (Triangular src2530) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2530_2399 : (Triangular src2530) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2530_2415 : (Triangular src2530) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2530_2457 : (Triangular src2530) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2530 : Cover (Triangular src2530) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2530_2390, by decide, by decide, pass2530_2391, by decide, by decide, pass2530_2393, by decide, by decide, pass2530_2399, by decide, by decide, pass2530_2415, by decide, by decide, pass2530_2457, rfl⟩
def src2531 : Request := ⟨⟨⟨2600,3628,798,25698⟩,535425056505856,4816500515660⟩,25,3,1,385610,22⟩
private theorem pass2531_2390 : (Triangular src2531) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2531_2391 : (Triangular src2531) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2531_2393 : (Triangular src2531) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2531_2398 : (Triangular src2531) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2531_2411 : (Triangular src2531) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2531_2445 : (Triangular src2531) 2445 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2531 : Cover (Triangular src2531) 2534 2390 [2390,2392,2397,2410,2444,2534] := by
  exact ⟨by decide, by decide, pass2531_2390, by decide, by decide, pass2531_2391, by decide, by decide, pass2531_2393, by decide, by decide, pass2531_2398, by decide, by decide, pass2531_2411, by decide, by decide, pass2531_2445, rfl⟩
def src2532 : Request := ⟨⟨⟨5700,7953,1750,55476⟩,5637370734182400,111115710437454⟩,65,3,1,385610,22⟩
private theorem pass2532_2390 : (Triangular src2532) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2532_2391 : (Triangular src2532) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2532_2393 : (Triangular src2532) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2532_2398 : (Triangular src2532) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2532_2411 : (Triangular src2532) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2532_2445 : (Triangular src2532) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2532_2533 : (Triangular src2532) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2532 : Cover (Triangular src2532) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2532_2390, by decide, by decide, pass2532_2391, by decide, by decide, pass2532_2393, by decide, by decide, pass2532_2398, by decide, by decide, pass2532_2411, by decide, by decide, pass2532_2445, by decide, by decide, pass2532_2533, rfl⟩
def src2533 : Request := ⟨⟨⟨6900,9626,2077,87320⟩,9849424459857920,234809190715807⟩,110,3,1,385610,22⟩
private theorem pass2533_2390 : (Triangular src2533) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2533_2391 : (Triangular src2533) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2533_2393 : (Triangular src2533) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2533_2398 : (Triangular src2533) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2533_2411 : (Triangular src2533) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2533_2445 : (Triangular src2533) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2533_2533 : (Triangular src2533) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2533 : Cover (Triangular src2533) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2533_2390, by decide, by decide, pass2533_2391, by decide, by decide, pass2533_2393, by decide, by decide, pass2533_2398, by decide, by decide, pass2533_2411, by decide, by decide, pass2533_2445, by decide, by decide, pass2533_2533, rfl⟩
def src2534 : Request := ⟨⟨⟨10000,13953,3010,96583⟩,29974681586237440,1036125345444439⟩,110,3,1,385610,22⟩
private theorem pass2534_2390 : (Triangular src2534) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2534_2391 : (Triangular src2534) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2534_2393 : (Triangular src2534) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2534_2398 : (Triangular src2534) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2534_2411 : (Triangular src2534) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2534_2445 : (Triangular src2534) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2534_2533 : (Triangular src2534) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2534 : Cover (Triangular src2534) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2534_2390, by decide, by decide, pass2534_2391, by decide, by decide, pass2534_2393, by decide, by decide, pass2534_2398, by decide, by decide, pass2534_2411, by decide, by decide, pass2534_2445, by decide, by decide, pass2534_2533, rfl⟩
def src2535 : Request := ⟨⟨⟨8300,11579,2498,114528⟩,17139238515245056,491470625461013⟩,145,3,1,385610,22⟩
private theorem pass2535_2390 : (Triangular src2535) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2535_2391 : (Triangular src2535) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2535_2393 : (Triangular src2535) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2535_2398 : (Triangular src2535) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2535_2411 : (Triangular src2535) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2535_2445 : (Triangular src2535) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2535_2533 : (Triangular src2535) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2535 : Cover (Triangular src2535) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2535_2390, by decide, by decide, pass2535_2391, by decide, by decide, pass2535_2393, by decide, by decide, pass2535_2398, by decide, by decide, pass2535_2411, by decide, by decide, pass2535_2445, by decide, by decide, pass2535_2533, rfl⟩
def src2536 : Request := ⟨⟨⟨1000,1395,307,8170⟩,30557599170560,105715278267⟩,0,3,1,385610,23⟩
private theorem pass2536_2390 : (Triangular src2536) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2536_2391 : (Triangular src2536) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2536_2393 : (Triangular src2536) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2536_2399 : (Triangular src2536) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2536_2415 : (Triangular src2536) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2536_2459 : (Triangular src2536) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2536 : Cover (Triangular src2536) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2536_2390, by decide, by decide, pass2536_2391, by decide, by decide, pass2536_2393, by decide, by decide, pass2536_2399, by decide, by decide, pass2536_2415, by decide, by decide, pass2536_2459, rfl⟩
def src2537 : Request := ⟨⟨⟨1000,1395,307,8450⟩,30557599170560,105715278267⟩,1,3,1,385610,23⟩
private theorem pass2537_2390 : (Triangular src2537) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2537_2391 : (Triangular src2537) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2537_2393 : (Triangular src2537) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2537_2399 : (Triangular src2537) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2537_2415 : (Triangular src2537) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2537_2459 : (Triangular src2537) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2537 : Cover (Triangular src2537) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2537_2390, by decide, by decide, pass2537_2391, by decide, by decide, pass2537_2393, by decide, by decide, pass2537_2399, by decide, by decide, pass2537_2415, by decide, by decide, pass2537_2459, rfl⟩
def src2538 : Request := ⟨⟨⟨1000,1395,301,9094⟩,30103476895744,104105680031⟩,2,3,1,385610,23⟩
private theorem pass2538_2390 : (Triangular src2538) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2538_2391 : (Triangular src2538) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2538_2393 : (Triangular src2538) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2538_2399 : (Triangular src2538) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2538_2415 : (Triangular src2538) 2415 2459 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2538_2460 : (Triangular src2538) 2460 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2538 : Cover (Triangular src2538) 2534 2390 [2390,2392,2398,2414,2459,2534] := by
  exact ⟨by decide, by decide, pass2538_2390, by decide, by decide, pass2538_2391, by decide, by decide, pass2538_2393, by decide, by decide, pass2538_2399, by decide, by decide, pass2538_2415, by decide, by decide, pass2538_2460, rfl⟩
def src2539 : Request := ⟨⟨⟨1200,1674,368,10390⟩,52718727069696,218807905514⟩,4,3,1,385610,23⟩
private theorem pass2539_2390 : (Triangular src2539) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2539_2391 : (Triangular src2539) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2539_2393 : (Triangular src2539) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2539_2399 : (Triangular src2539) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2539_2415 : (Triangular src2539) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2539_2458 : (Triangular src2539) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2539 : Cover (Triangular src2539) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2539_2390, by decide, by decide, pass2539_2391, by decide, by decide, pass2539_2393, by decide, by decide, pass2539_2399, by decide, by decide, pass2539_2415, by decide, by decide, pass2539_2458, rfl⟩
def src2540 : Request := ⟨⟨⟨1450,2023,445,12899⟩,92998964346880,466511127281⟩,8,3,1,385610,23⟩
private theorem pass2540_2390 : (Triangular src2540) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2540_2391 : (Triangular src2540) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2540_2393 : (Triangular src2540) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2540_2399 : (Triangular src2540) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2540_2415 : (Triangular src2540) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2540_2458 : (Triangular src2540) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2540 : Cover (Triangular src2540) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2540_2390, by decide, by decide, pass2540_2391, by decide, by decide, pass2540_2393, by decide, by decide, pass2540_2399, by decide, by decide, pass2540_2415, by decide, by decide, pass2540_2458, rfl⟩
def src2541 : Request := ⟨⟨⟨2100,2930,645,20119⟩,282396798484480,2051392203643⟩,20,3,1,385610,23⟩
private theorem pass2541_2390 : (Triangular src2541) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2541_2391 : (Triangular src2541) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2541_2393 : (Triangular src2541) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2541_2398 : (Triangular src2541) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2541_2412 : (Triangular src2541) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2541_2449 : (Triangular src2541) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2541 : Cover (Triangular src2541) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2541_2390, by decide, by decide, pass2541_2391, by decide, by decide, pass2541_2393, by decide, by decide, pass2541_2398, by decide, by decide, pass2541_2412, by decide, by decide, pass2541_2449, rfl⟩
def src2542 : Request := ⟨⟨⟨4800,6697,1474,42722⟩,3367547627110400,55891290082931⟩,50,3,1,385610,23⟩
private theorem pass2542_2390 : (Triangular src2542) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2542_2391 : (Triangular src2542) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2542_2393 : (Triangular src2542) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2542_2398 : (Triangular src2542) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2542_2411 : (Triangular src2542) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2542_2445 : (Triangular src2542) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2542_2533 : (Triangular src2542) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2542 : Cover (Triangular src2542) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2542_2390, by decide, by decide, pass2542_2391, by decide, by decide, pass2542_2393, by decide, by decide, pass2542_2398, by decide, by decide, pass2542_2411, by decide, by decide, pass2542_2445, by decide, by decide, pass2542_2533, rfl⟩
def src2543 : Request := ⟨⟨⟨4800,6697,1474,48812⟩,3367547627110400,55891290082931⟩,65,3,1,385610,23⟩
private theorem pass2543_2390 : (Triangular src2543) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2543_2391 : (Triangular src2543) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2543_2393 : (Triangular src2543) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2543_2398 : (Triangular src2543) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2543_2411 : (Triangular src2543) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2543_2445 : (Triangular src2543) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2543_2533 : (Triangular src2543) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2543 : Cover (Triangular src2543) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2543_2390, by decide, by decide, pass2543_2391, by decide, by decide, pass2543_2393, by decide, by decide, pass2543_2398, by decide, by decide, pass2543_2411, by decide, by decide, pass2543_2445, by decide, by decide, pass2543_2533, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1980

-- Source: Research6969.PrefixRescueDataMiddle47
section Z6969Source1981
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle47
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,22⟩
  bank i := ![bank203 8042, bank221 9279, bank221 9655, bank228 10680, bank228 11023, bank237 13715, bank271 25698, bank346 55476, bank355 87320, bank382 96583, bank367 114528] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385610
  seedFloor := 22

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank203 8042
    · exact rank221 9279
    · exact rank221 9655
    · exact rank228 10680
    · exact rank228 11023
    · exact rank237 13715
    · exact rank271 25698
    · exact rank346 55476
    · exact rank355 87320
    · exact rank382 96583
    · exact rank367 114528
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2525⟩
    · exact ⟨_, cover2526⟩
    · exact ⟨_, cover2527⟩
    · exact ⟨_, cover2528⟩
    · exact ⟨_, cover2529⟩
    · exact ⟨_, cover2530⟩
    · exact ⟨_, cover2531⟩
    · exact ⟨_, cover2532⟩
    · exact ⟨_, cover2533⟩
    · exact ⟨_, cover2534⟩
    · exact ⟨_, cover2535⟩

def price : EarlyPrice := ⟨3, 22, 10, 80/100, 80/100, ![981934440000, 169103103187, 25806987500, 2346111390], 1374624428128934⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 84742/73, 299161/73, 1259808/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle47
end Z6969Source1981

-- Source: Research6969.PrefixMiddleSaved47
section Z6969Source1982
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved47
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle47.price Lower6960.Prefix6969RescueData.Middle47.price :=
  ⟨336, 3711, 113, 1160, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle47.plan Lower6960.Prefix6969RescueData.Middle47.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 22 22 :=
  ⟨Lower6960.Prefix6969MainCases.Middle47.plan, Lower6960.Prefix6969MainCases.Middle47.price, Lower6960.Prefix6969MainCases.Middle47.valid, Lower6960.Prefix6969MainCases.Middle47.priced, Lower6960.Prefix6969MainCases.Middle47.sources,
   Lower6960.Prefix6969RescueData.Middle47.plan, Lower6960.Prefix6969RescueData.Middle47.price, Lower6960.Prefix6969RescueData.Middle47.sources, Lower6960.Prefix6969RescueData.Middle47.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved47
end Z6969Source1982

-- Source: Research6969.PrefixMainDataMiddle48
section Z6969Source1983
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle48
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank149 5119, bank199 7608, bank180 21819, bank212 8810, bank170 28384] i
  head := src2945
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 124479, 579617, 2072821],
    ![25417/2, 95029, 431515, 2861677/2],
    ![54680/9, 137890/3, 431515, 2861677/2],
    ![29433/8, 223357/8, 2022460/9, 754728],
    ![63052/25, 479758/25, 157352, 2289169/4],
    ![5710/3, 14275, 582147/4, 483800],
    ![18775/16, 290125/32, 304304/3, 8940624/25],
    ![89110/121, 61800/11, 440200/7, 1485266/7],
    ![89110/121, 61800/11, 440200/7, 1485266/7],
    ![63754/121, 727364/147, 770661/16, 9535698/49],
    ![63754/121, 727364/147, 770661/16, 1658944/9],
    ![63754/121, 578323/121, 770661/16, 9114361/64],
    ![1355575/3362, 578323/121, 770661/16, 9114361/64],
    ![1355575/3362, 421963/100, 3844369/98, 26204161/196],
    ![1355575/3362, 1684700/441, 17075787/484, 13802814/121],
    ![25627/74, 1684700/441, 17075787/484, 13802814/121],
    ![25627/74, 10101721/2738, 45394195/1352, 13802814/121],
    ![920087/2738, 10101721/2738, 45394195/1352, 13802814/121]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 23 385610 := by
  refine ⟨?_, rank154 4838, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2945⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free35_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free84_1
    · exact free95_1
    · exact free137_1
    · exact free126_1
    · exact free149_1
    · exact free199_1
    · exact free180_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [247095932, 318844981, 318799168, 319158437, 320259467, 319677881, 319549375, 147094230, 147166767, 147105875, 147389078, 67486888, 64976107, 83599718, 92217476, 97457600, 147484919, 220712782], [1473674, 1095106, 1095340, 1093500, 1087862, 1090840, 1091498, 2618031, 2616824, 2617838, 2613124, 5958752, 6193476, 4773409, 4308185, 4066368, 2611529, 1690827],
  ![117158758941240, 1622345564228, 198641503800, 5126740150], 132913261888379792⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 10101721/2738, 45394195/1352, 13802814/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle48
end Z6969Source1983

-- Source: Research6969.PhysicalChecks159
section Z6969Source1984
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2544 : Request := ⟨⟨⟨6900,9626,2077,80758⟩,9849424459857920,234809190715807⟩,110,3,1,385610,23⟩
private theorem pass2544_2390 : (Triangular src2544) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2544_2391 : (Triangular src2544) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2544_2393 : (Triangular src2544) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2544_2398 : (Triangular src2544) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2544_2411 : (Triangular src2544) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2544_2445 : (Triangular src2544) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2544_2533 : (Triangular src2544) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2544 : Cover (Triangular src2544) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2544_2390, by decide, by decide, pass2544_2391, by decide, by decide, pass2544_2393, by decide, by decide, pass2544_2398, by decide, by decide, pass2544_2411, by decide, by decide, pass2544_2445, by decide, by decide, pass2544_2533, rfl⟩
def src2545 : Request := ⟨⟨⟨10000,13953,3070,87388⟩,30428373265940480,1052197377228338⟩,110,3,1,385610,23⟩
private theorem pass2545_2390 : (Triangular src2545) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2545_2391 : (Triangular src2545) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2545_2393 : (Triangular src2545) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2545_2398 : (Triangular src2545) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2545_2411 : (Triangular src2545) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2545_2444 : (Triangular src2545) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2545_2529 : (Triangular src2545) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2545 : Cover (Triangular src2545) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2545_2390, by decide, by decide, pass2545_2391, by decide, by decide, pass2545_2393, by decide, by decide, pass2545_2398, by decide, by decide, pass2545_2411, by decide, by decide, pass2545_2444, by decide, by decide, pass2545_2529, rfl⟩
def src2546 : Request := ⟨⟨⟨8300,11579,2498,105277⟩,17139238515245056,491470625461013⟩,145,3,1,385610,23⟩
private theorem pass2546_2390 : (Triangular src2546) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2546_2391 : (Triangular src2546) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2546_2393 : (Triangular src2546) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2546_2398 : (Triangular src2546) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2546_2411 : (Triangular src2546) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2546_2445 : (Triangular src2546) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2546_2533 : (Triangular src2546) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2546 : Cover (Triangular src2546) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2546_2390, by decide, by decide, pass2546_2391, by decide, by decide, pass2546_2393, by decide, by decide, pass2546_2398, by decide, by decide, pass2546_2411, by decide, by decide, pass2546_2445, by decide, by decide, pass2546_2533, rfl⟩
def src2547 : Request := ⟨⟨⟨825,1151,248,7156⟩,16903818182656,48256472894⟩,0,3,1,385610,24⟩
private theorem pass2547_2390 : (Triangular src2547) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2547_2391 : (Triangular src2547) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2547_2393 : (Triangular src2547) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2547_2399 : (Triangular src2547) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2547_2416 : (Triangular src2547) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2547_2464 : (Triangular src2547) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2547 : Cover (Triangular src2547) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2547_2390, by decide, by decide, pass2547_2391, by decide, by decide, pass2547_2393, by decide, by decide, pass2547_2399, by decide, by decide, pass2547_2416, by decide, by decide, pass2547_2464, rfl⟩
def src2548 : Request := ⟨⟨⟨1000,1395,307,8014⟩,30557599170560,105715278267⟩,1,3,1,385610,24⟩
private theorem pass2548_2390 : (Triangular src2548) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2548_2391 : (Triangular src2548) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2548_2393 : (Triangular src2548) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2548_2399 : (Triangular src2548) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2548_2415 : (Triangular src2548) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2548_2459 : (Triangular src2548) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2548 : Cover (Triangular src2548) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2548_2390, by decide, by decide, pass2548_2391, by decide, by decide, pass2548_2393, by decide, by decide, pass2548_2399, by decide, by decide, pass2548_2415, by decide, by decide, pass2548_2459, rfl⟩
def src2549 : Request := ⟨⟨⟨1000,1395,301,8600⟩,30103476895744,104105680031⟩,2,3,1,385610,24⟩
private theorem pass2549_2390 : (Triangular src2549) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2549_2391 : (Triangular src2549) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2549_2393 : (Triangular src2549) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2549_2399 : (Triangular src2549) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2549_2415 : (Triangular src2549) 2415 2459 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2549_2460 : (Triangular src2549) 2460 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2549 : Cover (Triangular src2549) 2534 2390 [2390,2392,2398,2414,2459,2534] := by
  exact ⟨by decide, by decide, pass2549_2390, by decide, by decide, pass2549_2391, by decide, by decide, pass2549_2393, by decide, by decide, pass2549_2399, by decide, by decide, pass2549_2415, by decide, by decide, pass2549_2460, rfl⟩
def src2550 : Request := ⟨⟨⟨1200,1674,368,9837⟩,52718727069696,218807905514⟩,4,3,1,385610,24⟩
private theorem pass2550_2390 : (Triangular src2550) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2550_2391 : (Triangular src2550) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2550_2393 : (Triangular src2550) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2550_2399 : (Triangular src2550) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2550_2415 : (Triangular src2550) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2550_2458 : (Triangular src2550) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2550 : Cover (Triangular src2550) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2550_2390, by decide, by decide, pass2550_2391, by decide, by decide, pass2550_2393, by decide, by decide, pass2550_2399, by decide, by decide, pass2550_2415, by decide, by decide, pass2550_2458, rfl⟩
def src2551 : Request := ⟨⟨⟨1450,2023,445,12186⟩,92998964346880,466511127281⟩,8,3,1,385610,24⟩
private theorem pass2551_2390 : (Triangular src2551) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2551_2391 : (Triangular src2551) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2551_2393 : (Triangular src2551) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2551_2399 : (Triangular src2551) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2551_2415 : (Triangular src2551) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2551_2458 : (Triangular src2551) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2551 : Cover (Triangular src2551) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2551_2390, by decide, by decide, pass2551_2391, by decide, by decide, pass2551_2393, by decide, by decide, pass2551_2399, by decide, by decide, pass2551_2415, by decide, by decide, pass2551_2458, rfl⟩
def src2552 : Request := ⟨⟨⟨2100,2930,645,18896⟩,282396798484480,2051392203643⟩,20,3,1,385610,24⟩
private theorem pass2552_2390 : (Triangular src2552) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2552_2391 : (Triangular src2552) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2552_2393 : (Triangular src2552) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2552_2398 : (Triangular src2552) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2552_2412 : (Triangular src2552) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2552_2449 : (Triangular src2552) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2552 : Cover (Triangular src2552) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2552_2390, by decide, by decide, pass2552_2391, by decide, by decide, pass2552_2393, by decide, by decide, pass2552_2398, by decide, by decide, pass2552_2412, by decide, by decide, pass2552_2449, rfl⟩
def src2553 : Request := ⟨⟨⟨5700,7953,1750,49097⟩,5637370734182400,111115710437454⟩,65,3,1,385610,24⟩
private theorem pass2553_2390 : (Triangular src2553) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2553_2391 : (Triangular src2553) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2553_2393 : (Triangular src2553) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2553_2398 : (Triangular src2553) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2553_2411 : (Triangular src2553) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2553_2445 : (Triangular src2553) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2553_2533 : (Triangular src2553) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2553 : Cover (Triangular src2553) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2553_2390, by decide, by decide, pass2553_2391, by decide, by decide, pass2553_2393, by decide, by decide, pass2553_2398, by decide, by decide, pass2553_2411, by decide, by decide, pass2553_2445, by decide, by decide, pass2553_2533, rfl⟩
def src2554 : Request := ⟨⟨⟨6900,9626,2118,71278⟩,9997036108906496,238415548481346⟩,110,3,1,385610,24⟩
private theorem pass2554_2390 : (Triangular src2554) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2554_2391 : (Triangular src2554) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2554_2393 : (Triangular src2554) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2554_2398 : (Triangular src2554) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2554_2411 : (Triangular src2554) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2554_2445 : (Triangular src2554) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2554_2532 : (Triangular src2554) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2554 : Cover (Triangular src2554) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2554_2390, by decide, by decide, pass2554_2391, by decide, by decide, pass2554_2393, by decide, by decide, pass2554_2398, by decide, by decide, pass2554_2411, by decide, by decide, pass2554_2445, by decide, by decide, pass2554_2532, rfl⟩
def src2555 : Request := ⟨⟨⟨8300,11580,2548,75105⟩,17399709518790656,499263802703202⟩,110,3,1,385610,24⟩
private theorem pass2555_2390 : (Triangular src2555) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2555_2391 : (Triangular src2555) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2555_2393 : (Triangular src2555) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2555_2398 : (Triangular src2555) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2555_2411 : (Triangular src2555) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2555_2445 : (Triangular src2555) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2555_2532 : (Triangular src2555) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2555 : Cover (Triangular src2555) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2555_2390, by decide, by decide, pass2555_2391, by decide, by decide, pass2555_2393, by decide, by decide, pass2555_2398, by decide, by decide, pass2555_2411, by decide, by decide, pass2555_2445, by decide, by decide, pass2555_2532, rfl⟩
def src2556 : Request := ⟨⟨⟨10000,13953,3070,82687⟩,30428373265940480,1052197377228338⟩,110,3,1,385610,24⟩
private theorem pass2556_2390 : (Triangular src2556) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2556_2391 : (Triangular src2556) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2556_2393 : (Triangular src2556) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2556_2398 : (Triangular src2556) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2556_2411 : (Triangular src2556) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2556_2444 : (Triangular src2556) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2556_2529 : (Triangular src2556) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2556 : Cover (Triangular src2556) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2556_2390, by decide, by decide, pass2556_2391, by decide, by decide, pass2556_2393, by decide, by decide, pass2556_2398, by decide, by decide, pass2556_2411, by decide, by decide, pass2556_2444, by decide, by decide, pass2556_2529, rfl⟩
def src2557 : Request := ⟨⟨⟨8300,11579,2498,97084⟩,17139238515245056,491470625461013⟩,145,3,1,385610,24⟩
private theorem pass2557_2390 : (Triangular src2557) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2557_2391 : (Triangular src2557) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2557_2393 : (Triangular src2557) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2557_2398 : (Triangular src2557) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2557_2411 : (Triangular src2557) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2557_2445 : (Triangular src2557) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2557_2533 : (Triangular src2557) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2557 : Cover (Triangular src2557) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2557_2390, by decide, by decide, pass2557_2391, by decide, by decide, pass2557_2393, by decide, by decide, pass2557_2398, by decide, by decide, pass2557_2411, by decide, by decide, pass2557_2445, by decide, by decide, pass2557_2533, rfl⟩
def src2558 : Request := ⟨⟨⟨690,963,208,6159⟩,9921631092736,23724874690⟩,0,3,1,385610,25⟩
private theorem pass2558_2390 : (Triangular src2558) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2558_2391 : (Triangular src2558) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2558_2393 : (Triangular src2558) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2558_2399 : (Triangular src2558) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2558_2416 : (Triangular src2558) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2558_2465 : (Triangular src2558) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2558 : Cover (Triangular src2558) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2558_2390, by decide, by decide, pass2558_2391, by decide, by decide, pass2558_2393, by decide, by decide, pass2558_2399, by decide, by decide, pass2558_2416, by decide, by decide, pass2558_2465, rfl⟩
def src2559 : Request := ⟨⟨⟨825,1151,248,7085⟩,16903818182656,48256472894⟩,1,3,1,385610,25⟩
private theorem pass2559_2390 : (Triangular src2559) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2559_2391 : (Triangular src2559) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2559_2393 : (Triangular src2559) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2559_2399 : (Triangular src2559) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2559_2416 : (Triangular src2559) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2559_2464 : (Triangular src2559) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2559 : Cover (Triangular src2559) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2559_2390, by decide, by decide, pass2559_2391, by decide, by decide, pass2559_2393, by decide, by decide, pass2559_2399, by decide, by decide, pass2559_2416, by decide, by decide, pass2559_2464, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1984

-- Source: Research6969.PrefixRescueDataMiddle48
section Z6969Source1985
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle48
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,23⟩
  bank i := ![bank222 8170, bank222 8450, bank221 9094, bank228 10390, bank237 12899, bank253 20119, bank329 42722, bank329 48812, bank383 87388, bank355 80758, bank367 105277] i
  reserve i := ![0, 1, 2, 4, 8, 20, 50, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385610
  seedFloor := 23

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank222 8170
    · exact rank222 8450
    · exact rank221 9094
    · exact rank228 10390
    · exact rank237 12899
    · exact rank253 20119
    · exact rank329 42722
    · exact rank329 48812
    · exact rank383 87388
    · exact rank355 80758
    · exact rank367 105277
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2536⟩
    · exact ⟨_, cover2537⟩
    · exact ⟨_, cover2538⟩
    · exact ⟨_, cover2539⟩
    · exact ⟨_, cover2540⟩
    · exact ⟨_, cover2541⟩
    · exact ⟨_, cover2542⟩
    · exact ⟨_, cover2543⟩
    · exact ⟨_, cover2545⟩
    · exact ⟨_, cover2544⟩
    · exact ⟨_, cover2546⟩

def price : EarlyPrice := ⟨3, 23, 10, 75/100, 70/100, ![943646704805, 165663004927, 27517837550, 2392877730], 1475426822220419⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 162731/146, 291074/73, 2421371/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle48
end Z6969Source1985

-- Source: Research6969.PrefixMiddleSaved48
section Z6969Source1986
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved48
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle48.price Lower6960.Prefix6969RescueData.Middle48.price :=
  ⟨336, 3689, 113, 1114, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle48.plan Lower6960.Prefix6969RescueData.Middle48.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 23 23 :=
  ⟨Lower6960.Prefix6969MainCases.Middle48.plan, Lower6960.Prefix6969MainCases.Middle48.price, Lower6960.Prefix6969MainCases.Middle48.valid, Lower6960.Prefix6969MainCases.Middle48.priced, Lower6960.Prefix6969MainCases.Middle48.sources,
   Lower6960.Prefix6969RescueData.Middle48.plan, Lower6960.Prefix6969RescueData.Middle48.price, Lower6960.Prefix6969RescueData.Middle48.sources, Lower6960.Prefix6969RescueData.Middle48.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved48
end Z6969Source1986

-- Source: Research6969.PrefixMainDataMiddle49
section Z6969Source1987
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle49
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 40, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank129 10859, bank151 5065, bank212 8810, bank186 19684, bank175 25973, bank169 29097] i
  head := src2946
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15511, 124729, 578536, 2029349],
    ![25417/2, 188985/2, 429079, 1413685],
    ![54680/9, 411350/9, 429079, 1413685],
    ![29433/8, 111055/4, 2011208/9, 745680],
    ![63052/25, 95418/5, 157352, 2289169/4],
    ![17323/9, 85595/6, 144389, 1896465/4],
    ![18775/16, 144265/16, 304304/3, 1766688/5],
    ![89110/121, 676030/121, 437764/7, 1467460/7],
    ![89110/121, 676030/121, 116003/2, 1467460/7],
    ![63754/121, 724000/147, 770661/16, 9421380/49],
    ![63754/121, 724000/147, 770661/16, 535360/3],
    ![63754/121, 574611/121, 770661/16, 9114361/64],
    ![33263/82, 574611/121, 770661/16, 9114361/64],
    ![33263/82, 168321/40, 3874725/98, 25654225/196],
    ![33263/82, 5021730/1369, 22567685/676, 294782600/2601],
    ![481425/1369, 5021730/1369, 22567685/676, 294782600/2601],
    ![929061/2738, 5021730/1369, 22567685/676, 294782600/2601],
    ![459151/1369, 5021730/1369, 22567685/676, 294782600/2601]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 24 385610 := by
  refine ⟨?_, rank154 4780, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2946⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free129_1
    · exact free151_1
    · exact free212_1
    · exact free186_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [247580558, 319861335, 320154543, 319392088, 317845377, 319089361, 318341639, 146815879, 146915063, 146867026, 146923616, 67443733, 69805957, 78355777, 96937676, 112491699, 129986415, 230660451], [1469685, 1089901, 1088399, 1092304, 1100225, 1093854, 1097683, 2623351, 2621174, 2622228, 2620986, 5962667, 5748364, 5104986, 4088335, 3495315, 2992734, 1608950],
  ![122439180599820, 1611551760084, 207594405900, 6074933340], 135153710878292348⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5021730/1369, 22567685/676, 294782600/2601] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle49
end Z6969Source1987

end Merged_Z6969Pack0744

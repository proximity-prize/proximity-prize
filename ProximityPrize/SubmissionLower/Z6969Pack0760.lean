import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0753
import ProximityPrize.SubmissionLower.Z6969Pack0750
import ProximityPrize.SubmissionLower.Z6969Pack0752
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0747
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0737
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0754
section Merged_Z6969Pack0754

-- Source: Research6969.PrefixMiddleSaved73
section Z6969Source2096
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved73
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle73.price Lower6960.Prefix6969RescueData.Middle73.price :=
  ⟨335, 3236, 58, 640, true⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle73.plan Lower6960.Prefix6969RescueData.Middle73.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    exact ⟨by decide, by decide +kernel⟩
  · rw [Budget.extra, Budget.adjust]
    decide +kernel

def data : Case 4 53 56 :=
  ⟨Lower6960.Prefix6969MainCases.Middle73.plan, Lower6960.Prefix6969MainCases.Middle73.price, Lower6960.Prefix6969MainCases.Middle73.valid, Lower6960.Prefix6969MainCases.Middle73.priced, Lower6960.Prefix6969MainCases.Middle73.sources,
   Lower6960.Prefix6969RescueData.Middle73.plan, Lower6960.Prefix6969RescueData.Middle73.price, Lower6960.Prefix6969RescueData.Middle73.sources, Lower6960.Prefix6969RescueData.Middle73.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved73
end Z6969Source2096

-- Source: Research6969.PrefixMiddleSelect4
section Z6969Source2097
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer
set_option maxHeartbeats 8000000

theorem choose4 (j : Fin 56) :
    ∃ l u : ℕ, l≤j.val+1 ∧ j.val+1≤u ∧ Nonempty (Case 4 l u) := by
  fin_cases j
  · exact ⟨1, 1, by decide, by decide, ⟨Saved2.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved3.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved3.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved4.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved4.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved4.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved4.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved4.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved5.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved6.data⟩⟩
  · exact ⟨26, 29, by decide, by decide, ⟨Saved66.data⟩⟩
  · exact ⟨26, 29, by decide, by decide, ⟨Saved66.data⟩⟩
  · exact ⟨26, 29, by decide, by decide, ⟨Saved66.data⟩⟩
  · exact ⟨26, 29, by decide, by decide, ⟨Saved66.data⟩⟩
  · exact ⟨30, 33, by decide, by decide, ⟨Saved67.data⟩⟩
  · exact ⟨30, 33, by decide, by decide, ⟨Saved67.data⟩⟩
  · exact ⟨30, 33, by decide, by decide, ⟨Saved67.data⟩⟩
  · exact ⟨30, 33, by decide, by decide, ⟨Saved67.data⟩⟩
  · exact ⟨34, 37, by decide, by decide, ⟨Saved68.data⟩⟩
  · exact ⟨34, 37, by decide, by decide, ⟨Saved68.data⟩⟩
  · exact ⟨34, 37, by decide, by decide, ⟨Saved68.data⟩⟩
  · exact ⟨34, 37, by decide, by decide, ⟨Saved68.data⟩⟩
  · exact ⟨38, 40, by decide, by decide, ⟨Saved69.data⟩⟩
  · exact ⟨38, 40, by decide, by decide, ⟨Saved69.data⟩⟩
  · exact ⟨38, 40, by decide, by decide, ⟨Saved69.data⟩⟩
  · exact ⟨41, 44, by decide, by decide, ⟨Saved70.data⟩⟩
  · exact ⟨41, 44, by decide, by decide, ⟨Saved70.data⟩⟩
  · exact ⟨41, 44, by decide, by decide, ⟨Saved70.data⟩⟩
  · exact ⟨41, 44, by decide, by decide, ⟨Saved70.data⟩⟩
  · exact ⟨45, 48, by decide, by decide, ⟨Saved71.data⟩⟩
  · exact ⟨45, 48, by decide, by decide, ⟨Saved71.data⟩⟩
  · exact ⟨45, 48, by decide, by decide, ⟨Saved71.data⟩⟩
  · exact ⟨45, 48, by decide, by decide, ⟨Saved71.data⟩⟩
  · exact ⟨49, 52, by decide, by decide, ⟨Saved72.data⟩⟩
  · exact ⟨49, 52, by decide, by decide, ⟨Saved72.data⟩⟩
  · exact ⟨49, 52, by decide, by decide, ⟨Saved72.data⟩⟩
  · exact ⟨49, 52, by decide, by decide, ⟨Saved72.data⟩⟩
  · exact ⟨53, 56, by decide, by decide, ⟨Saved73.data⟩⟩
  · exact ⟨53, 56, by decide, by decide, ⟨Saved73.data⟩⟩
  · exact ⟨53, 56, by decide, by decide, ⟨Saved73.data⟩⟩
  · exact ⟨53, 56, by decide, by decide, ⟨Saved73.data⟩⟩

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source2097

-- Source: Research6969.PhysicalChecks195
section Z6969Source2098
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3120 : Request := ⟨⟨⟨400,558,123,3437⟩,1971918995456,2734096379⟩,6,6,1,771221,41⟩
private theorem pass3120_2390 : (Triangular src3120) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3120_2391 : (Triangular src3120) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3120_2394 : (Triangular src3120) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3120_2403 : (Triangular src3120) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3120_2431 : (Triangular src3120) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3120_2517 : (Triangular src3120) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3120 : Cover (Triangular src3120) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass3120_2390, by decide, by decide, pass3120_2391, by decide, by decide, pass3120_2394, by decide, by decide, pass3120_2403, by decide, by decide, pass3120_2431, by decide, by decide, pass3120_2517, rfl⟩
def src3121 : Request := ⟨⟨⟨560,781,172,4950⟩,5388141854720,10440670587⟩,13,6,1,771221,41⟩
private theorem pass3121_2390 : (Triangular src3121) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3121_2391 : (Triangular src3121) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3121_2393 : (Triangular src3121) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3121_2399 : (Triangular src3121) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3121_2417 : (Triangular src3121) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3121_2469 : (Triangular src3121) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3121 : Cover (Triangular src3121) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3121_2390, by decide, by decide, pass3121_2391, by decide, by decide, pass3121_2393, by decide, by decide, pass3121_2399, by decide, by decide, pass3121_2417, by decide, by decide, pass3121_2469, rfl⟩
def src3122 : Request := ⟨⟨⟨1200,1673,378,10568⟩,53798525730816,222977190790⟩,40,6,1,771221,41⟩
private theorem pass3122_2390 : (Triangular src3122) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3122_2391 : (Triangular src3122) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3122_2393 : (Triangular src3122) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3122_2399 : (Triangular src3122) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3122_2415 : (Triangular src3122) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3122_2458 : (Triangular src3122) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3122 : Cover (Triangular src3122) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3122_2390, by decide, by decide, pass3122_2391, by decide, by decide, pass3122_2393, by decide, by decide, pass3122_2399, by decide, by decide, pass3122_2415, by decide, by decide, pass3122_2458, rfl⟩
def src3123 : Request := ⟨⟨⟨1450,2021,445,19132⟩,92998964346880,465028319332⟩,65,6,1,771221,41⟩
private theorem pass3123_2390 : (Triangular src3123) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3123_2391 : (Triangular src3123) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3123_2393 : (Triangular src3123) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3123_2399 : (Triangular src3123) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3123_2415 : (Triangular src3123) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3123_2458 : (Triangular src3123) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3123 : Cover (Triangular src3123) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3123_2390, by decide, by decide, pass3123_2391, by decide, by decide, pass3123_2393, by decide, by decide, pass3123_2399, by decide, by decide, pass3123_2415, by decide, by decide, pass3123_2458, rfl⟩
def src3124 : Request := ⟨⟨⟨1750,2440,537,16270⟩,163381988556800,986966790957⟩,65,6,1,771221,41⟩
private theorem pass3124_2390 : (Triangular src3124) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3124_2391 : (Triangular src3124) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3124_2393 : (Triangular src3124) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3124_2399 : (Triangular src3124) 2399 2413 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3124_2414 : (Triangular src3124) 2414 2453 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3124_2454 : (Triangular src3124) 2454 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3124 : Cover (Triangular src3124) 2534 2390 [2390,2392,2398,2413,2453,2534] := by
  exact ⟨by decide, by decide, pass3124_2390, by decide, by decide, pass3124_2391, by decide, by decide, pass3124_2393, by decide, by decide, pass3124_2399, by decide, by decide, pass3124_2414, by decide, by decide, pass3124_2454, rfl⟩
def src3125 : Request := ⟨⟨⟨4800,6692,1474,42990⟩,3367547627110400,55757027345056⟩,190,6,1,771221,41⟩
private theorem pass3125_2390 : (Triangular src3125) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3125_2391 : (Triangular src3125) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3125_2393 : (Triangular src3125) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3125_2398 : (Triangular src3125) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3125_2411 : (Triangular src3125) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3125_2445 : (Triangular src3125) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3125_2533 : (Triangular src3125) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3125 : Cover (Triangular src3125) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3125_2390, by decide, by decide, pass3125_2391, by decide, by decide, pass3125_2393, by decide, by decide, pass3125_2398, by decide, by decide, pass3125_2411, by decide, by decide, pass3125_2445, by decide, by decide, pass3125_2533, rfl⟩
def src3126 : Request := ⟨⟨⟨4800,6690,1512,66149⟩,3433136573644800,56816483122989⟩,245,6,1,771221,41⟩
private theorem pass3126_2390 : (Triangular src3126) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3126_2391 : (Triangular src3126) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3126_2393 : (Triangular src3126) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3126_2398 : (Triangular src3126) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3126_2411 : (Triangular src3126) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3126_2445 : (Triangular src3126) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3126_2533 : (Triangular src3126) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3126 : Cover (Triangular src3126) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3126_2390, by decide, by decide, pass3126_2391, by decide, by decide, pass3126_2393, by decide, by decide, pass3126_2398, by decide, by decide, pass3126_2411, by decide, by decide, pass3126_2445, by decide, by decide, pass3126_2533, rfl⟩
def src3127 : Request := ⟨⟨⟨556,772,170,5588⟩,5255817068544,9968090926⟩,10,6,2,771220,2⟩
private theorem pass3127_2390 : (Triangular src3127) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3127_2391 : (Triangular src3127) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3127_2393 : (Triangular src3127) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3127_2399 : (Triangular src3127) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3127_2417 : (Triangular src3127) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3127_2469 : (Triangular src3127) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3127 : Cover (Triangular src3127) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3127_2390, by decide, by decide, pass3127_2391, by decide, by decide, pass3127_2393, by decide, by decide, pass3127_2399, by decide, by decide, pass3127_2417, by decide, by decide, pass3127_2469, rfl⟩
def src3128 : Request := ⟨⟨⟨556,772,170,5533⟩,5255817068544,9968090926⟩,10,6,2,771220,3⟩
private theorem pass3128_2390 : (Triangular src3128) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3128_2391 : (Triangular src3128) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3128_2394 : (Triangular src3128) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3128_2402 : (Triangular src3128) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3128_2426 : (Triangular src3128) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3128_2496 : (Triangular src3128) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3128 : Cover (Triangular src3128) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3128_2390, by decide, by decide, pass3128_2391, by decide, by decide, pass3128_2394, by decide, by decide, pass3128_2402, by decide, by decide, pass3128_2426, by decide, by decide, pass3128_2496, rfl⟩
def src3129 : Request := ⟨⟨⟨556,772,170,5423⟩,5255817068544,9968090926⟩,10,6,2,771220,5⟩
private theorem pass3129_2390 : (Triangular src3129) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3129_2391 : (Triangular src3129) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3129_2394 : (Triangular src3129) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3129_2402 : (Triangular src3129) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3129_2426 : (Triangular src3129) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3129_2496 : (Triangular src3129) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3129 : Cover (Triangular src3129) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3129_2390, by decide, by decide, pass3129_2391, by decide, by decide, pass3129_2394, by decide, by decide, pass3129_2402, by decide, by decide, pass3129_2426, by decide, by decide, pass3129_2496, rfl⟩
def src3130 : Request := ⟨⟨⟨556,772,170,5156⟩,5255817068544,9968090926⟩,10,6,2,771220,10⟩
private theorem pass3130_2390 : (Triangular src3130) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3130_2391 : (Triangular src3130) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3130_2393 : (Triangular src3130) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3130_2399 : (Triangular src3130) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3130_2417 : (Triangular src3130) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3130_2469 : (Triangular src3130) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3130 : Cover (Triangular src3130) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3130_2390, by decide, by decide, pass3130_2391, by decide, by decide, pass3130_2393, by decide, by decide, pass3130_2399, by decide, by decide, pass3130_2417, by decide, by decide, pass3130_2469, rfl⟩
def src3131 : Request := ⟨⟨⟨556,772,170,4806⟩,5255817068544,9968090926⟩,10,6,2,771220,17⟩
private theorem pass3131_2390 : (Triangular src3131) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3131_2391 : (Triangular src3131) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3131_2394 : (Triangular src3131) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3131_2402 : (Triangular src3131) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3131_2426 : (Triangular src3131) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3131_2496 : (Triangular src3131) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3131 : Cover (Triangular src3131) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3131_2390, by decide, by decide, pass3131_2391, by decide, by decide, pass3131_2394, by decide, by decide, pass3131_2402, by decide, by decide, pass3131_2426, by decide, by decide, pass3131_2496, rfl⟩
def src3132 : Request := ⟨⟨⟨556,772,170,4358⟩,5255817068544,9968090926⟩,10,6,2,771220,27⟩
private theorem pass3132_2390 : (Triangular src3132) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3132_2391 : (Triangular src3132) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3132_2393 : (Triangular src3132) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3132_2399 : (Triangular src3132) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3132_2417 : (Triangular src3132) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3132_2469 : (Triangular src3132) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3132 : Cover (Triangular src3132) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3132_2390, by decide, by decide, pass3132_2391, by decide, by decide, pass3132_2393, by decide, by decide, pass3132_2399, by decide, by decide, pass3132_2417, by decide, by decide, pass3132_2469, rfl⟩
def src3133 : Request := ⟨⟨⟨556,772,170,3832⟩,5255817068544,9968090926⟩,10,6,2,771220,42⟩
private theorem pass3133_2390 : (Triangular src3133) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3133_2391 : (Triangular src3133) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3133_2393 : (Triangular src3133) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3133_2399 : (Triangular src3133) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3133_2417 : (Triangular src3133) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3133_2469 : (Triangular src3133) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3133 : Cover (Triangular src3133) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3133_2390, by decide, by decide, pass3133_2391, by decide, by decide, pass3133_2393, by decide, by decide, pass3133_2399, by decide, by decide, pass3133_2417, by decide, by decide, pass3133_2469, rfl⟩
def src3134 : Request := ⟨⟨⟨325,453,100,4013⟩,1061047500800,1193036697⟩,0,7,1,899758,1⟩
private theorem pass3134_2390 : (Triangular src3134) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3134_2391 : (Triangular src3134) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3134_2394 : (Triangular src3134) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3134_2403 : (Triangular src3134) 2403 2432 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3134_2433 : (Triangular src3134) 2433 2529 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3134_2530 : (Triangular src3134) 2530 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3134 : Cover (Triangular src3134) 2534 2390 [2390,2393,2402,2432,2529,2534] := by
  exact ⟨by decide, by decide, pass3134_2390, by decide, by decide, pass3134_2391, by decide, by decide, pass3134_2394, by decide, by decide, pass3134_2403, by decide, by decide, pass3134_2433, by decide, by decide, pass3134_2530, rfl⟩
def src3135 : Request := ⟨⟨⟨325,453,100,4313⟩,1061047500800,1193036697⟩,1,7,1,899758,1⟩
private theorem pass3135_2390 : (Triangular src3135) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3135_2391 : (Triangular src3135) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3135_2394 : (Triangular src3135) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3135_2403 : (Triangular src3135) 2403 2432 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3135_2433 : (Triangular src3135) 2433 2529 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3135_2530 : (Triangular src3135) 2530 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3135 : Cover (Triangular src3135) 2534 2390 [2390,2393,2402,2432,2529,2534] := by
  exact ⟨by decide, by decide, pass3135_2390, by decide, by decide, pass3135_2391, by decide, by decide, pass3135_2394, by decide, by decide, pass3135_2403, by decide, by decide, pass3135_2433, by decide, by decide, pass3135_2530, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2098

-- Source: Research6969.PrefixMainDataMiddle7
section Z6969Source2099
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle7
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 65, 75] i
  bank i := ![bank3 1102, bank10 1206, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank89 2959, bank123 3043, bank83 3955, bank147 5174, bank198 7884, bank158 18445, bank171 27879] i
  head := src3127
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 128855, 597087, 2172720],
    ![24861/2, 101547, 463263, 1684782],
    ![29433/8, 119741/4, 2167960/9, 871728],
    ![17323/9, 30821/2, 311705/2, 2217039/4],
    ![81680/81, 220220/27, 743798/9, 891286/3],
    ![81680/81, 220220/27, 743798/9, 891286/3],
    ![250508/361, 2034252/361, 9162032/169, 33069784/169],
    ![250508/361, 612193/121, 203881/4, 34008568/225],
    ![254619/484, 612193/121, 771225/16, 34008568/225],
    ![254619/484, 451797/100, 2032362/49, 7228078/49],
    ![658228/1323, 5385152/1323, 969272/27, 3263392/25],
    ![480716/1323, 5385152/1323, 969272/27, 3263392/25],
    ![1826342/5329, 5385152/1323, 969272/27, 3263392/25]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 1 642684 := by
  refine ⟨?_, rank154 5588, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3127⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free89_3
    · exact free123_1
    · exact free83_3
    · exact free147_1
    · exact free198_1
    · exact free158_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [266471820, 342336983, 342095259, 341651499, 148981215, 148821790, 148605402, 94646905, 69731375, 76263372, 94574267, 90490397, 227597640], [1363327, 1009359, 1010022, 1011239, 2586624, 2589277, 2592879, 4185544, 5755130, 5249651, 4189210, 4395371, 1634159],
  ![120813379264800, 1614874930140, 204837876000, 5354644020], 147777178388154414⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 5385152/1323, 969272/27, 3263392/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle7
end Z6969Source2099

-- Source: Research6969.PrefixRescueDataMiddle7
section Z6969Source2100
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle7
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,5,1,1⟩
  bank i := ![bank134 7489, bank141 8551, bank141 9210, bank155 10669, bank193 13347, bank221 17883, bank233 26175, bank232 32318, bank249 37466, bank364 153796] i
  reserve i := ![0, 1, 2, 4, 8, 13, 25, 32, 40, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 1

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 7489
    · exact rank141 8551
    · exact rank141 9210
    · exact rank155 10669
    · exact rank193 13347
    · exact rank221 17883
    · exact rank233 26175
    · exact rank232 32318
    · exact rank249 37466
    · exact rank364 153796
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2964⟩
    · exact ⟨_, cover2965⟩
    · exact ⟨_, cover2966⟩
    · exact ⟨_, cover2967⟩
    · exact ⟨_, cover2968⟩
    · exact ⟨_, cover2969⟩
    · exact ⟨_, cover2970⟩
    · exact ⟨_, cover2971⟩
    · exact ⟨_, cover2972⟩
    · exact ⟨_, cover2973⟩

def price : EarlyPrice := ⟨5, 1, 9, 95/100, 80/100, ![59937377120, 243286238400, 973520560, 3894057260], 517731343873346⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![21569/191, 156294/191, 780557/191, 153796/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle7
end Z6969Source2100

-- Source: Research6969.PrefixMiddleSaved7
section Z6969Source2101
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved7
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle7.price Lower6960.Prefix6969RescueData.Middle7.price :=
  ⟨342, 4070, 112, 818, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle7.plan Lower6960.Prefix6969RescueData.Middle7.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 5 1 1 :=
  ⟨Lower6960.Prefix6969MainCases.Middle7.plan, Lower6960.Prefix6969MainCases.Middle7.price, Lower6960.Prefix6969MainCases.Middle7.valid, Lower6960.Prefix6969MainCases.Middle7.priced, Lower6960.Prefix6969MainCases.Middle7.sources,
   Lower6960.Prefix6969RescueData.Middle7.plan, Lower6960.Prefix6969RescueData.Middle7.price, Lower6960.Prefix6969RescueData.Middle7.sources, Lower6960.Prefix6969RescueData.Middle7.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved7
end Z6969Source2101

-- Source: Research6969.PrefixMainDataMiddle8
section Z6969Source2102
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle8
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 15, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1102, bank10 1206, bank24 1404, bank36 1602, bank42 1886, bank52 2212, bank65 2772, bank93 2467, bank83 3955, bank139 4010, bank198 7884, bank158 18445, bank171 27879] i
  head := src3128
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15193, 128342, 595561, 2186662],
    ![24861/2, 101052, 1843977/4, 3336399/2],
    ![29433/8, 476599/16, 2157290/9, 863148],
    ![34345/18, 274495/18, 2492735/16, 4431933/8],
    ![36739/32, 309701/32, 909052/9, 3556996/9],
    ![86036/121, 724619/121, 3273503/49, 1748428/7],
    ![86036/121, 724619/121, 3273503/49, 1748428/7],
    ![86036/121, 724619/121, 3273503/49, 2481802/11],
    ![254619/484, 2307442/441, 771225/16, 3126145/14],
    ![254619/484, 733693/150, 6581510/147, 22187330/147],
    ![658228/1323, 5358532/1323, 4822622/135, 3231272/25],
    ![480716/1323, 5358532/1323, 4822622/135, 3231272/25],
    ![1826342/5329, 5358532/1323, 4822622/135, 3231272/25]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 2 642684 := by
  refine ⟨?_, rank154 5533, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3128⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free24_1
    · exact free36_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free93_1
    · exact free83_3
    · exact free139_1
    · exact free198_1
    · exact free158_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [262570123, 337487812, 337985126, 338058650, 336708622, 140380645, 138248320, 72503796, 106860691, 80799497, 99340597, 106349669, 227373309], [1383308, 1022663, 1021298, 1021097, 1024800, 2764595, 2811396, 5533120, 3691003, 4939866, 3986809, 3708762, 1636006],
  ![120694299883380, 1615118651676, 204635978100, 5038663320], 145648358510444141⟩

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
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 5358532/1323, 4822622/135, 3231272/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle8
end Z6969Source2102

-- Source: Research6969.PhysicalChecks186
section Z6969Source2103
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2976 : Request := ⟨⟨⟨560,781,169,9239⟩,5316921262080,10299257375⟩,2,5,1,642684,2⟩
private theorem pass2976_2390 : (Triangular src2976) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2976_2391 : (Triangular src2976) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2976_2393 : (Triangular src2976) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2976_2399 : (Triangular src2976) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2976_2417 : (Triangular src2976) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2976_2469 : (Triangular src2976) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2976 : Cover (Triangular src2976) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2976_2390, by decide, by decide, pass2976_2391, by decide, by decide, pass2976_2393, by decide, by decide, pass2976_2399, by decide, by decide, pass2976_2417, by decide, by decide, pass2976_2469, rfl⟩
def src2977 : Request := ⟨⟨⟨560,781,169,9785⟩,5316921262080,10299257375⟩,3,5,1,642684,2⟩
private theorem pass2977_2390 : (Triangular src2977) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2977_2391 : (Triangular src2977) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2977_2393 : (Triangular src2977) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2977_2399 : (Triangular src2977) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2977_2417 : (Triangular src2977) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2977_2469 : (Triangular src2977) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2977 : Cover (Triangular src2977) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2977_2390, by decide, by decide, pass2977_2391, by decide, by decide, pass2977_2393, by decide, by decide, pass2977_2399, by decide, by decide, pass2977_2417, by decide, by decide, pass2977_2469, rfl⟩
def src2978 : Request := ⟨⟨⟨560,781,169,10399⟩,5316921262080,10299257375⟩,4,5,1,642684,2⟩
private theorem pass2978_2390 : (Triangular src2978) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2978_2391 : (Triangular src2978) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2978_2393 : (Triangular src2978) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2978_2399 : (Triangular src2978) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2978_2417 : (Triangular src2978) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2978_2469 : (Triangular src2978) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2978 : Cover (Triangular src2978) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2978_2390, by decide, by decide, pass2978_2391, by decide, by decide, pass2978_2393, by decide, by decide, pass2978_2399, by decide, by decide, pass2978_2417, by decide, by decide, pass2978_2469, rfl⟩
def src2979 : Request := ⟨⟨⟨690,962,208,13330⟩,9921631092736,23645774460⟩,8,5,1,642684,2⟩
private theorem pass2979_2390 : (Triangular src2979) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2979_2391 : (Triangular src2979) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2979_2393 : (Triangular src2979) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2979_2399 : (Triangular src2979) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2979_2416 : (Triangular src2979) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2979_2465 : (Triangular src2979) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2979 : Cover (Triangular src2979) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2979_2390, by decide, by decide, pass2979_2391, by decide, by decide, pass2979_2393, by decide, by decide, pass2979_2399, by decide, by decide, pass2979_2416, by decide, by decide, pass2979_2465, rfl⟩
def src2980 : Request := ⟨⟨⟨1000,1395,307,15486⟩,30557599170560,105715278267⟩,10,5,1,642684,2⟩
private theorem pass2980_2390 : (Triangular src2980) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2980_2391 : (Triangular src2980) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2980_2393 : (Triangular src2980) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2980_2399 : (Triangular src2980) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2980_2415 : (Triangular src2980) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2980_2459 : (Triangular src2980) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2980 : Cover (Triangular src2980) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2980_2390, by decide, by decide, pass2980_2391, by decide, by decide, pass2980_2393, by decide, by decide, pass2980_2399, by decide, by decide, pass2980_2415, by decide, by decide, pass2980_2459, rfl⟩
def src2981 : Request := ⟨⟨⟨1450,2022,445,25505⟩,92998964346880,465769321795⟩,25,5,1,642684,2⟩
private theorem pass2981_2390 : (Triangular src2981) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2981_2391 : (Triangular src2981) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2981_2393 : (Triangular src2981) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2981_2399 : (Triangular src2981) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2981_2415 : (Triangular src2981) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2981_2457 : (Triangular src2981) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2981 : Cover (Triangular src2981) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2981_2390, by decide, by decide, pass2981_2391, by decide, by decide, pass2981_2393, by decide, by decide, pass2981_2399, by decide, by decide, pass2981_2415, by decide, by decide, pass2981_2457, rfl⟩
def src2982 : Request := ⟨⟨⟨2100,2929,645,36507⟩,282396798484480,2049139102608⟩,40,5,1,642684,2⟩
private theorem pass2982_2390 : (Triangular src2982) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2982_2391 : (Triangular src2982) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2982_2393 : (Triangular src2982) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2982_2398 : (Triangular src2982) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2982_2412 : (Triangular src2982) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2982_2448 : (Triangular src2982) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2982 : Cover (Triangular src2982) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2982_2390, by decide, by decide, pass2982_2391, by decide, by decide, pass2982_2393, by decide, by decide, pass2982_2398, by decide, by decide, pass2982_2412, by decide, by decide, pass2982_2448, rfl⟩
def src2983 : Request := ⟨⟨⟨2100,2928,645,60108⟩,282396798484480,2046887686018⟩,65,5,1,642684,2⟩
private theorem pass2983_2390 : (Triangular src2983) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2983_2391 : (Triangular src2983) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2983_2393 : (Triangular src2983) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2983_2398 : (Triangular src2983) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2983_2412 : (Triangular src2983) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2983_2448 : (Triangular src2983) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2983 : Cover (Triangular src2983) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2983_2390, by decide, by decide, pass2983_2391, by decide, by decide, pass2983_2393, by decide, by decide, pass2983_2398, by decide, by decide, pass2983_2412, by decide, by decide, pass2983_2448, rfl⟩
def src2984 : Request := ⟨⟨⟨5700,7951,1750,90765⟩,5637370734182400,111025751789870⟩,110,5,1,642684,2⟩
private theorem pass2984_2390 : (Triangular src2984) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2984_2391 : (Triangular src2984) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2984_2393 : (Triangular src2984) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2984_2398 : (Triangular src2984) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2984_2411 : (Triangular src2984) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2984_2445 : (Triangular src2984) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2984_2532 : (Triangular src2984) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2984 : Cover (Triangular src2984) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2984_2390, by decide, by decide, pass2984_2391, by decide, by decide, pass2984_2393, by decide, by decide, pass2984_2398, by decide, by decide, pass2984_2411, by decide, by decide, pass2984_2445, by decide, by decide, pass2984_2532, rfl⟩
def src2985 : Request := ⟨⟨⟨470,655,144,7181⟩,3184589537280,5168862572⟩,0,5,1,642684,4⟩
private theorem pass2985_2390 : (Triangular src2985) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2985_2391 : (Triangular src2985) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2985_2394 : (Triangular src2985) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2985_2403 : (Triangular src2985) 2403 2428 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2985_2429 : (Triangular src2985) 2429 2506 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2985_2507 : (Triangular src2985) 2507 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2985 : Cover (Triangular src2985) 2534 2390 [2390,2393,2402,2428,2506,2534] := by
  exact ⟨by decide, by decide, pass2985_2390, by decide, by decide, pass2985_2391, by decide, by decide, pass2985_2394, by decide, by decide, pass2985_2403, by decide, by decide, pass2985_2429, by decide, by decide, pass2985_2507, rfl⟩
def src2986 : Request := ⟨⟨⟨470,655,144,7680⟩,3184589537280,5168862572⟩,1,5,1,642684,4⟩
private theorem pass2986_2390 : (Triangular src2986) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2986_2391 : (Triangular src2986) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2986_2393 : (Triangular src2986) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2986_2399 : (Triangular src2986) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2986_2417 : (Triangular src2986) 2417 2470 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2986_2471 : (Triangular src2986) 2471 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2986 : Cover (Triangular src2986) 2534 2390 [2390,2392,2398,2416,2470,2534] := by
  exact ⟨by decide, by decide, pass2986_2390, by decide, by decide, pass2986_2391, by decide, by decide, pass2986_2393, by decide, by decide, pass2986_2399, by decide, by decide, pass2986_2417, by decide, by decide, pass2986_2471, rfl⟩
def src2987 : Request := ⟨⟨⟨470,655,144,8255⟩,3184589537280,5168862572⟩,2,5,1,642684,4⟩
private theorem pass2987_2390 : (Triangular src2987) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2987_2391 : (Triangular src2987) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2987_2394 : (Triangular src2987) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2987_2402 : (Triangular src2987) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2987_2426 : (Triangular src2987) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2987_2498 : (Triangular src2987) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2987 : Cover (Triangular src2987) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass2987_2390, by decide, by decide, pass2987_2391, by decide, by decide, pass2987_2394, by decide, by decide, pass2987_2402, by decide, by decide, pass2987_2426, by decide, by decide, pass2987_2498, rfl⟩
def src2988 : Request := ⟨⟨⟨470,655,144,8923⟩,3184589537280,5168862572⟩,3,5,1,642684,4⟩
private theorem pass2988_2390 : (Triangular src2988) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2988_2391 : (Triangular src2988) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2988_2394 : (Triangular src2988) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2988_2402 : (Triangular src2988) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2988_2426 : (Triangular src2988) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2988_2498 : (Triangular src2988) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2988 : Cover (Triangular src2988) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass2988_2390, by decide, by decide, pass2988_2391, by decide, by decide, pass2988_2394, by decide, by decide, pass2988_2402, by decide, by decide, pass2988_2426, by decide, by decide, pass2988_2498, rfl⟩
def src2989 : Request := ⟨⟨⟨470,655,144,9708⟩,3184589537280,5168862572⟩,4,5,1,642684,4⟩
private theorem pass2989_2390 : (Triangular src2989) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2989_2391 : (Triangular src2989) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2989_2393 : (Triangular src2989) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2989_2399 : (Triangular src2989) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2989_2417 : (Triangular src2989) 2417 2470 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2989_2471 : (Triangular src2989) 2471 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2989 : Cover (Triangular src2989) 2534 2390 [2390,2392,2398,2416,2470,2534] := by
  exact ⟨by decide, by decide, pass2989_2390, by decide, by decide, pass2989_2391, by decide, by decide, pass2989_2393, by decide, by decide, pass2989_2399, by decide, by decide, pass2989_2417, by decide, by decide, pass2989_2471, rfl⟩
def src2990 : Request := ⟨⟨⟨690,962,212,12325⟩,10065769922560,23997864317⟩,8,5,1,642684,4⟩
private theorem pass2990_2390 : (Triangular src2990) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2990_2391 : (Triangular src2990) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2990_2393 : (Triangular src2990) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2990_2399 : (Triangular src2990) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2990_2416 : (Triangular src2990) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2990_2464 : (Triangular src2990) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2990 : Cover (Triangular src2990) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2990_2390, by decide, by decide, pass2990_2391, by decide, by decide, pass2990_2393, by decide, by decide, pass2990_2399, by decide, by decide, pass2990_2416, by decide, by decide, pass2990_2464, rfl⟩
def src2991 : Request := ⟨⟨⟨1200,1674,368,18530⟩,52718727069696,218807905514⟩,16,5,1,642684,4⟩
private theorem pass2991_2390 : (Triangular src2991) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2991_2391 : (Triangular src2991) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2991_2393 : (Triangular src2991) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2991_2399 : (Triangular src2991) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2991_2415 : (Triangular src2991) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2991_2458 : (Triangular src2991) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2991 : Cover (Triangular src2991) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2991_2390, by decide, by decide, pass2991_2391, by decide, by decide, pass2991_2393, by decide, by decide, pass2991_2399, by decide, by decide, pass2991_2415, by decide, by decide, pass2991_2458, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2103

-- Source: Research6969.PrefixRescueDataMiddle8
section Z6969Source2104
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle8
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,3⟩
  bank i := ![bank133 7522, bank134 7986, bank155 9239, bank155 9785, bank155 10399, bank192 13330, bank222 15486, bank233 25505, bank249 36507, bank247 60108, bank340 90765] i
  reserve i := ![0, 1, 2, 3, 4, 8, 10, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 2

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank133 7522
    · exact rank134 7986
    · exact rank155 9239
    · exact rank155 9785
    · exact rank155 10399
    · exact rank192 13330
    · exact rank222 15486
    · exact rank233 25505
    · exact rank249 36507
    · exact rank247 60108
    · exact rank340 90765
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2974⟩
    · exact ⟨_, cover2975⟩
    · exact ⟨_, cover2976⟩
    · exact ⟨_, cover2977⟩
    · exact ⟨_, cover2978⟩
    · exact ⟨_, cover2979⟩
    · exact ⟨_, cover2980⟩
    · exact ⟨_, cover2981⟩
    · exact ⟨_, cover2982⟩
    · exact ⟨_, cover2983⟩
    · exact ⟨_, cover2984⟩

def price : EarlyPrice := ⟨5, 3, 10, 95/100, 80/100, ![106118081280, 148740747102, 2046016000, 2728022500], 475076943703562⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![918/11, 865, 159226/37, 90765/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle8
end Z6969Source2104

-- Source: Research6969.PrefixMiddleSaved8
section Z6969Source2105
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved8
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle8.price Lower6960.Prefix6969RescueData.Middle8.price :=
  ⟨342, 4050, 83, 865, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle8.plan Lower6960.Prefix6969RescueData.Middle8.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 5 2 3 :=
  ⟨Lower6960.Prefix6969MainCases.Middle8.plan, Lower6960.Prefix6969MainCases.Middle8.price, Lower6960.Prefix6969MainCases.Middle8.valid, Lower6960.Prefix6969MainCases.Middle8.priced, Lower6960.Prefix6969MainCases.Middle8.sources,
   Lower6960.Prefix6969RescueData.Middle8.plan, Lower6960.Prefix6969RescueData.Middle8.price, Lower6960.Prefix6969RescueData.Middle8.sources, Lower6960.Prefix6969RescueData.Middle8.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved8
end Z6969Source2105

-- Source: Research6969.PrefixMainDataMiddle9
section Z6969Source2106
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle9
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank89 2959, bank123 3043, bank83 3955, bank147 5174, bank158 18445, bank211 8704, bank171 27879] i
  head := src3129
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 128360, 594282, 2151930],
    ![24861/2, 100062, 1825827/4, 3270069/2],
    ![29433/8, 471869/16, 2135950/9, 845988],
    ![17323/9, 60707/4, 2456185/16, 8606301/16],
    ![81680/81, 216920/27, 732743/9, 1729937/6],
    ![81680/81, 216920/27, 732743/9, 1729937/6],
    ![250508/361, 105468/19, 9026402/169, 32093314/169],
    ![250508/361, 602293/121, 203881/4, 33004378/225],
    ![254619/484, 602293/121, 771225/16, 33004378/225],
    ![254619/484, 889899/200, 2001837/49, 14029301/98],
    ![480716/1323, 889899/200, 2001837/49, 14029301/98],
    ![480716/1323, 21138684/5329, 22055936/625, 20650784/169],
    ![1826342/5329, 21138684/5329, 22055936/625, 20650784/169]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 4 642684 := by
  refine ⟨?_, rank154 5423, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3129⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free89_3
    · exact free123_1
    · exact free83_3
    · exact free147_1
    · exact free158_1
    · exact free211_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [263116380, 338734367, 337918107, 337290004, 148971301, 149070477, 149092363, 40779823, 70080973, 74859810, 103493640, 86377217, 226708625], [1380511, 1019243, 1021482, 1023205, 2586789, 2585138, 2584774, 9985144, 5725889, 5346691, 3811339, 4608303, 1641476],
  ![120341472322500, 1615839414820, 204037762500, 5483880570], 145491886786306830⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 26 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 21138684/5329, 22055936/625, 20650784/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle9
end Z6969Source2106

-- Source: Research6969.PhysicalChecks187
section Z6969Source2107
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2992 : Request := ⟨⟨⟨1750,2441,537,29066⟩,163381988556800,988269431527⟩,32,5,1,642684,4⟩
private theorem pass2992_2390 : (Triangular src2992) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2992_2391 : (Triangular src2992) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2992_2393 : (Triangular src2992) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2992_2398 : (Triangular src2992) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2992_2412 : (Triangular src2992) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2992_2449 : (Triangular src2992) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2992 : Cover (Triangular src2992) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2992_2390, by decide, by decide, pass2992_2391, by decide, by decide, pass2992_2393, by decide, by decide, pass2992_2398, by decide, by decide, pass2992_2412, by decide, by decide, pass2992_2449, rfl⟩
def src2993 : Request := ⟨⟨⟨3950,5510,1189,67606⟩,1848744952463360,25226292539926⟩,85,5,1,642684,4⟩
private theorem pass2993_2390 : (Triangular src2993) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2993_2391 : (Triangular src2993) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2993_2393 : (Triangular src2993) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2993_2398 : (Triangular src2993) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2993_2411 : (Triangular src2993) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2993_2445 : (Triangular src2993) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2993_2534 : (Triangular src2993) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2993 : Cover (Triangular src2993) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2993_2390, by decide, by decide, pass2993_2391, by decide, by decide, pass2993_2393, by decide, by decide, pass2993_2398, by decide, by decide, pass2993_2411, by decide, by decide, pass2993_2445, by decide, by decide, pass2993_2534, rfl⟩
def src2994 : Request := ⟨⟨⟨3200,4462,982,96179⟩,997767489781760,11020095796464⟩,110,5,1,642684,4⟩
private theorem pass2994_2390 : (Triangular src2994) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2994_2391 : (Triangular src2994) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2994_2393 : (Triangular src2994) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2994_2398 : (Triangular src2994) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2994_2411 : (Triangular src2994) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2994_2445 : (Triangular src2994) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2994_2534 : (Triangular src2994) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2994 : Cover (Triangular src2994) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2994_2390, by decide, by decide, pass2994_2391, by decide, by decide, pass2994_2393, by decide, by decide, pass2994_2398, by decide, by decide, pass2994_2411, by decide, by decide, pass2994_2445, by decide, by decide, pass2994_2534, rfl⟩
def src2995 : Request := ⟨⟨⟨8300,11577,2548,137972⟩,17399709518790656,498847383098023⟩,190,5,1,642684,4⟩
private theorem pass2995_2390 : (Triangular src2995) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2995_2391 : (Triangular src2995) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2995_2393 : (Triangular src2995) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2995_2398 : (Triangular src2995) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2995_2411 : (Triangular src2995) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2995_2444 : (Triangular src2995) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2995_2529 : (Triangular src2995) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2995 : Cover (Triangular src2995) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2995_2390, by decide, by decide, pass2995_2391, by decide, by decide, pass2995_2393, by decide, by decide, pass2995_2398, by decide, by decide, pass2995_2411, by decide, by decide, pass2995_2444, by decide, by decide, pass2995_2529, rfl⟩
def src2996 : Request := ⟨⟨⟨400,558,123,5994⟩,1971918995456,2734096379⟩,0,5,1,642684,9⟩
private theorem pass2996_2390 : (Triangular src2996) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2996_2391 : (Triangular src2996) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2996_2394 : (Triangular src2996) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2996_2403 : (Triangular src2996) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2996_2430 : (Triangular src2996) 2430 2512 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2996_2513 : (Triangular src2996) 2513 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2996 : Cover (Triangular src2996) 2534 2390 [2390,2393,2402,2429,2512,2534] := by
  exact ⟨by decide, by decide, pass2996_2390, by decide, by decide, pass2996_2391, by decide, by decide, pass2996_2394, by decide, by decide, pass2996_2403, by decide, by decide, pass2996_2430, by decide, by decide, pass2996_2513, rfl⟩
def src2997 : Request := ⟨⟨⟨470,655,141,6874⟩,3134317133824,5085275599⟩,1,5,1,642684,9⟩
private theorem pass2997_2390 : (Triangular src2997) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2997_2391 : (Triangular src2997) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2997_2394 : (Triangular src2997) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2997_2403 : (Triangular src2997) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2997_2430 : (Triangular src2997) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2997_2511 : (Triangular src2997) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2997 : Cover (Triangular src2997) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2997_2390, by decide, by decide, pass2997_2391, by decide, by decide, pass2997_2394, by decide, by decide, pass2997_2403, by decide, by decide, pass2997_2430, by decide, by decide, pass2997_2511, rfl⟩
def src2998 : Request := ⟨⟨⟨470,655,141,8011⟩,3134317133824,5085275599⟩,3,5,1,642684,9⟩
private theorem pass2998_2390 : (Triangular src2998) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2998_2391 : (Triangular src2998) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2998_2394 : (Triangular src2998) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2998_2403 : (Triangular src2998) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2998_2430 : (Triangular src2998) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2998_2511 : (Triangular src2998) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2998 : Cover (Triangular src2998) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2998_2390, by decide, by decide, pass2998_2391, by decide, by decide, pass2998_2394, by decide, by decide, pass2998_2403, by decide, by decide, pass2998_2430, by decide, by decide, pass2998_2511, rfl⟩
def src2999 : Request := ⟨⟨⟨690,962,212,10681⟩,10065769922560,23997864317⟩,8,5,1,642684,9⟩
private theorem pass2999_2390 : (Triangular src2999) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2999_2391 : (Triangular src2999) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2999_2393 : (Triangular src2999) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2999_2399 : (Triangular src2999) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2999_2416 : (Triangular src2999) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2999_2464 : (Triangular src2999) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2999 : Cover (Triangular src2999) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2999_2390, by decide, by decide, pass2999_2391, by decide, by decide, pass2999_2393, by decide, by decide, pass2999_2399, by decide, by decide, pass2999_2416, by decide, by decide, pass2999_2464, rfl⟩
def src3000 : Request := ⟨⟨⟨1200,1673,368,20843⟩,52718727069696,218387554859⟩,25,5,1,642684,9⟩
private theorem pass3000_2390 : (Triangular src3000) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3000_2391 : (Triangular src3000) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3000_2393 : (Triangular src3000) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3000_2399 : (Triangular src3000) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3000_2415 : (Triangular src3000) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3000_2458 : (Triangular src3000) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3000 : Cover (Triangular src3000) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3000_2390, by decide, by decide, pass3000_2391, by decide, by decide, pass3000_2393, by decide, by decide, pass3000_2399, by decide, by decide, pass3000_2415, by decide, by decide, pass3000_2458, rfl⟩
def src3001 : Request := ⟨⟨⟨2100,2929,645,30028⟩,282396798484480,2049139102608⟩,40,5,1,642684,9⟩
private theorem pass3001_2390 : (Triangular src3001) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3001_2391 : (Triangular src3001) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3001_2393 : (Triangular src3001) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3001_2398 : (Triangular src3001) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3001_2412 : (Triangular src3001) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3001_2448 : (Triangular src3001) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3001 : Cover (Triangular src3001) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass3001_2390, by decide, by decide, pass3001_2391, by decide, by decide, pass3001_2393, by decide, by decide, pass3001_2398, by decide, by decide, pass3001_2412, by decide, by decide, pass3001_2448, rfl⟩
def src3002 : Request := ⟨⟨⟨2600,3625,798,63834⟩,535425056505856,4803689494279⟩,85,5,1,642684,9⟩
private theorem pass3002_2390 : (Triangular src3002) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3002_2391 : (Triangular src3002) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3002_2393 : (Triangular src3002) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3002_2398 : (Triangular src3002) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3002_2411 : (Triangular src3002) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3002_2445 : (Triangular src3002) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3002_2534 : (Triangular src3002) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3002 : Cover (Triangular src3002) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3002_2390, by decide, by decide, pass3002_2391, by decide, by decide, pass3002_2393, by decide, by decide, pass3002_2398, by decide, by decide, pass3002_2411, by decide, by decide, pass3002_2445, by decide, by decide, pass3002_2534, rfl⟩
def src3003 : Request := ⟨⟨⟨4800,6692,1474,165879⟩,3367547627110400,55757027345056⟩,190,5,1,642684,9⟩
private theorem pass3003_2390 : (Triangular src3003) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3003_2391 : (Triangular src3003) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3003_2393 : (Triangular src3003) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3003_2398 : (Triangular src3003) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3003_2411 : (Triangular src3003) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3003_2445 : (Triangular src3003) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3003_2533 : (Triangular src3003) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3003 : Cover (Triangular src3003) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3003_2390, by decide, by decide, pass3003_2391, by decide, by decide, pass3003_2393, by decide, by decide, pass3003_2398, by decide, by decide, pass3003_2411, by decide, by decide, pass3003_2445, by decide, by decide, pass3003_2533, rfl⟩
def src3004 : Request := ⟨⟨⟨10000,13948,3070,151223⟩,30428373265940480,1050983571587703⟩,245,5,1,642684,9⟩
private theorem pass3004_2390 : (Triangular src3004) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3004_2391 : (Triangular src3004) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3004_2393 : (Triangular src3004) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3004_2398 : (Triangular src3004) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3004_2411 : (Triangular src3004) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3004_2444 : (Triangular src3004) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3004_2529 : (Triangular src3004) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3004 : Cover (Triangular src3004) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3004_2390, by decide, by decide, pass3004_2391, by decide, by decide, pass3004_2393, by decide, by decide, pass3004_2398, by decide, by decide, pass3004_2411, by decide, by decide, pass3004_2444, by decide, by decide, pass3004_2529, rfl⟩
def src3005 : Request := ⟨⟨⟨400,558,123,4812⟩,1971918995456,2734096379⟩,0,5,1,642684,16⟩
private theorem pass3005_2390 : (Triangular src3005) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3005_2391 : (Triangular src3005) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3005_2394 : (Triangular src3005) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3005_2403 : (Triangular src3005) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3005_2430 : (Triangular src3005) 2430 2513 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3005_2514 : (Triangular src3005) 2514 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3005 : Cover (Triangular src3005) 2534 2390 [2390,2393,2402,2429,2513,2534] := by
  exact ⟨by decide, by decide, pass3005_2390, by decide, by decide, pass3005_2391, by decide, by decide, pass3005_2394, by decide, by decide, pass3005_2403, by decide, by decide, pass3005_2430, by decide, by decide, pass3005_2514, rfl⟩
def src3006 : Request := ⟨⟨⟨470,655,141,5549⟩,3134317133824,5085275599⟩,1,5,1,642684,16⟩
private theorem pass3006_2390 : (Triangular src3006) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3006_2391 : (Triangular src3006) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3006_2394 : (Triangular src3006) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3006_2403 : (Triangular src3006) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3006_2430 : (Triangular src3006) 2430 2511 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3006_2512 : (Triangular src3006) 2512 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3006 : Cover (Triangular src3006) 2534 2390 [2390,2393,2402,2429,2511,2534] := by
  exact ⟨by decide, by decide, pass3006_2390, by decide, by decide, pass3006_2391, by decide, by decide, pass3006_2394, by decide, by decide, pass3006_2403, by decide, by decide, pass3006_2430, by decide, by decide, pass3006_2512, rfl⟩
def src3007 : Request := ⟨⟨⟨470,655,141,5956⟩,3134317133824,5085275599⟩,2,5,1,642684,16⟩
private theorem pass3007_2390 : (Triangular src3007) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3007_2391 : (Triangular src3007) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3007_2394 : (Triangular src3007) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3007_2403 : (Triangular src3007) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3007_2430 : (Triangular src3007) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3007_2511 : (Triangular src3007) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3007 : Cover (Triangular src3007) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass3007_2390, by decide, by decide, pass3007_2391, by decide, by decide, pass3007_2394, by decide, by decide, pass3007_2403, by decide, by decide, pass3007_2430, by decide, by decide, pass3007_2511, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2107

end Merged_Z6969Pack0754

-- merged module Z6969Pack0755
section Merged_Z6969Pack0755

-- Source: Research6969.PrefixRescueDataMiddle9
section Z6969Source2108
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle9
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,8⟩
  bank i := ![bank142 7181, bank142 7680, bank142 8255, bank142 8923, bank142 9708, bank193 12325, bank228 18530, bank242 29066, bank309 67606, bank296 96179, bank365 137972] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 85, 110, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 4

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 7181
    · exact rank142 7680
    · exact rank142 8255
    · exact rank142 8923
    · exact rank142 9708
    · exact rank193 12325
    · exact rank228 18530
    · exact rank242 29066
    · exact rank309 67606
    · exact rank296 96179
    · exact rank365 137972
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2985⟩
    · exact ⟨_, cover2986⟩
    · exact ⟨_, cover2987⟩
    · exact ⟨_, cover2988⟩
    · exact ⟨_, cover2989⟩
    · exact ⟨_, cover2990⟩
    · exact ⟨_, cover2991⟩
    · exact ⟨_, cover2992⟩
    · exact ⟨_, cover2993⟩
    · exact ⟨_, cover2994⟩
    · exact ⟨_, cover2995⟩

def price : EarlyPrice := ⟨5, 8, 10, 90/100, 80/100, ![430159443560, 243230395810, 7943976040, 3972000760], 704062568899308⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8390/111, 158356/191, 782476/191, 1103776/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle9
end Z6969Source2108

-- Source: Research6969.PrefixMiddleSaved9
section Z6969Source2109
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved9
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle9.price Lower6960.Prefix6969RescueData.Middle9.price :=
  ⟨342, 3966, 75, 829, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle9.plan Lower6960.Prefix6969RescueData.Middle9.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 5 4 8 :=
  ⟨Lower6960.Prefix6969MainCases.Middle9.plan, Lower6960.Prefix6969MainCases.Middle9.price, Lower6960.Prefix6969MainCases.Middle9.valid, Lower6960.Prefix6969MainCases.Middle9.priced, Lower6960.Prefix6969MainCases.Middle9.sources,
   Lower6960.Prefix6969RescueData.Middle9.plan, Lower6960.Prefix6969RescueData.Middle9.price, Lower6960.Prefix6969RescueData.Middle9.sources, Lower6960.Prefix6969RescueData.Middle9.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved9
end Z6969Source2109

-- Source: Research6969.PrefixMainDataMiddle10
section Z6969Source2110
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle10
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank89 2959, bank123 3043, bank83 3955, bank147 5174, bank158 18445, bank211 8704, bank171 27879] i
  head := src3130
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 127613, 590049, 2120556],
    ![24861/2, 97659, 445443, 1554534],
    ![29433/8, 115097/4, 2084152/9, 804336],
    ![17323/9, 29597/2, 299447/2, 2045643/4],
    ![81680/81, 211580/27, 714854/9, 822382/3],
    ![81680/81, 211580/27, 714854/9, 822382/3],
    ![250508/361, 1954764/361, 52112, 30513208/169],
    ![250508/361, 586273/121, 203881/4, 9259849/64],
    ![254619/484, 586273/121, 771225/16, 9259849/64],
    ![254619/484, 433869/100, 1952442/49, 6692569/49],
    ![480716/1323, 433869/100, 1952442/49, 6692569/49],
    ![480716/1323, 20607888/5329, 22055936/625, 18479104/153],
    ![1826342/5329, 20607888/5329, 22055936/625, 18479104/153]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 9 642684 := by
  refine ⟨?_, rank154 5156, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3130⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free89_3
    · exact free123_1
    · exact free83_3
    · exact free147_1
    · exact free158_1
    · exact free211_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [257771196, 331517077, 330499655, 330435805, 148383232, 148366630, 148490619, 36646026, 68969432, 72588592, 103853873, 86922526, 226381521], [1407885, 1039044, 1041835, 1042010, 2596577, 2596853, 2594789, 11134227, 5824254, 5526373, 3796119, 4575888, 1644169],
  ![120167838977220, 1616194703544, 203743368900, 5636900460], 141683230943144319⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 29 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 20607888/5329, 22055936/625, 18479104/153] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle10
end Z6969Source2110

-- Source: Research6969.PrefixRescueDataMiddle10
section Z6969Source2111
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle10
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,5,1,15⟩
  bank i := ![bank134 5994, bank141 6874, bank141 8011, bank193 10681, bank224 20843, bank249 30028, bank262 63834, bank375 151223, bank319 165879, bank375 151223] i
  reserve i := ![0, 1, 3, 8, 25, 40, 85, 245, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 9

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 5994
    · exact rank141 6874
    · exact rank141 8011
    · exact rank193 10681
    · exact rank224 20843
    · exact rank249 30028
    · exact rank262 63834
    · exact rank375 151223
    · exact rank319 165879
    · exact rank375 151223
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2996⟩
    · exact ⟨_, cover2997⟩
    · exact ⟨_, cover2998⟩
    · exact ⟨_, cover2999⟩
    · exact ⟨_, cover3000⟩
    · exact ⟨_, cover3001⟩
    · exact ⟨_, cover3002⟩
    · exact ⟨_, cover3004⟩
    · exact ⟨_, cover3003⟩
    · exact ⟨_, cover3004⟩

def price : EarlyPrice := ⟨5, 15, 9, 85/100, 70/100, ![969685505460, 299326957730, 17946421800, 4785730900], 855374303831738⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![12588/191, 197273/246, 965335/246, 756115/82] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle10
end Z6969Source2111

-- Source: Research6969.PrefixMiddleSaved10
section Z6969Source2112
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved10
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle10.price Lower6960.Prefix6969RescueData.Middle10.price :=
  ⟨342, 3867, 65, 801, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle10.plan Lower6960.Prefix6969RescueData.Middle10.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 5 9 15 :=
  ⟨Lower6960.Prefix6969MainCases.Middle10.plan, Lower6960.Prefix6969MainCases.Middle10.price, Lower6960.Prefix6969MainCases.Middle10.valid, Lower6960.Prefix6969MainCases.Middle10.priced, Lower6960.Prefix6969MainCases.Middle10.sources,
   Lower6960.Prefix6969RescueData.Middle10.plan, Lower6960.Prefix6969RescueData.Middle10.price, Lower6960.Prefix6969RescueData.Middle10.sources, Lower6960.Prefix6969RescueData.Middle10.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved10
end Z6969Source2112

-- Source: Research6969.PrefixMainDataMiddle11
section Z6969Source2113
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle11
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 75, 105, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank28 1523, bank37 1587, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank122 10626, bank159 5020, bank199 7608, bank187 16602, bank230 11634, bank172 23613, bank171 27879] i
  head := src3131
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 124927, 577622, 2096094],
    ![24861/2, 94509, 862011/2, 1454436],
    ![6218, 413966/9, 862011/2, 1454436],
    ![29433/8, 222669/8, 224028, 749736],
    ![62542/25, 479986/25, 312215/2, 2319529/4],
    ![17323/9, 42908/3, 1158063/8, 3813561/8],
    ![36739/32, 36259/4, 909052/9, 9064116/25],
    ![86036/121, 678818/121, 3067762/49, 1518696/7],
    ![86036/121, 678818/121, 3067762/49, 1518696/7],
    ![254619/484, 2180944/441, 771225/16, 1357695/7],
    ![254619/484, 2180944/441, 771225/16, 1357695/7],
    ![254619/484, 565273/121, 771225/16, 9259849/64],
    ![41249/100, 565273/121, 771225/16, 9259849/64],
    ![41249/100, 33889/8, 1960310/49, 6300100/49],
    ![41249/100, 1679260/441, 17021115/484, 13711518/121],
    ![1960504/5329, 1679260/441, 17021115/484, 13711518/121],
    ![1960504/5329, 189065/51, 14489285/432, 2762244/25],
    ![1872696/5329, 189065/51, 14489285/432, 2762244/25],
    ![1826342/5329, 189065/51, 14489285/432, 2762244/25]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 16 642684 := by
  refine ⟨?_, rank154 4806, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3131⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free28_1
    · exact free37_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free122_1
    · exact free159_1
    · exact free199_1
    · exact free187_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [245467764, 316345251, 315656929, 315717926, 315387921, 314963438, 316103421, 147449300, 147453511, 147289335, 147337548, 71621464, 71628157, 68001899, 80083973, 123470196, 100323696, 100000000, 224281661], [1487075, 1107908, 1111433, 1111120, 1112810, 1114984, 1109146, 2612121, 2612051, 2614784, 2613982, 5603322, 5602789, 5912030, 4985502, 3169940, 3945272, 3958949, 1661452],
  ![119053191292020, 1618472925364, 209899333200, 6030270600], 133956080348502046⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 189065/51, 14489285/432, 2762244/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle11
end Z6969Source2113

-- Source: Research6969.PhysicalChecks188
section Z6969Source2114
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3008 : Request := ⟨⟨⟨560,781,169,6902⟩,5316921262080,10299257375⟩,4,5,1,642684,16⟩
private theorem pass3008_2390 : (Triangular src3008) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3008_2391 : (Triangular src3008) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3008_2393 : (Triangular src3008) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3008_2399 : (Triangular src3008) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3008_2417 : (Triangular src3008) 2417 2469 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3008_2470 : (Triangular src3008) 2470 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3008 : Cover (Triangular src3008) 2534 2390 [2390,2392,2398,2416,2469,2534] := by
  exact ⟨by decide, by decide, pass3008_2390, by decide, by decide, pass3008_2391, by decide, by decide, pass3008_2393, by decide, by decide, pass3008_2399, by decide, by decide, pass3008_2417, by decide, by decide, pass3008_2470, rfl⟩
def src3009 : Request := ⟨⟨⟨690,962,212,8565⟩,10065769922560,23997864317⟩,8,5,1,642684,16⟩
private theorem pass3009_2390 : (Triangular src3009) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3009_2391 : (Triangular src3009) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3009_2393 : (Triangular src3009) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3009_2399 : (Triangular src3009) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3009_2416 : (Triangular src3009) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3009_2464 : (Triangular src3009) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3009 : Cover (Triangular src3009) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3009_2390, by decide, by decide, pass3009_2391, by decide, by decide, pass3009_2393, by decide, by decide, pass3009_2399, by decide, by decide, pass3009_2416, by decide, by decide, pass3009_2464, rfl⟩
def src3010 : Request := ⟨⟨⟨1000,1395,307,12404⟩,30557599170560,105715278267⟩,16,5,1,642684,16⟩
private theorem pass3010_2390 : (Triangular src3010) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3010_2391 : (Triangular src3010) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3010_2393 : (Triangular src3010) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3010_2399 : (Triangular src3010) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3010_2415 : (Triangular src3010) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3010_2459 : (Triangular src3010) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3010 : Cover (Triangular src3010) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3010_2390, by decide, by decide, pass3010_2391, by decide, by decide, pass3010_2393, by decide, by decide, pass3010_2399, by decide, by decide, pass3010_2415, by decide, by decide, pass3010_2459, rfl⟩
def src3011 : Request := ⟨⟨⟨1750,2441,537,23768⟩,163381988556800,988269431527⟩,40,5,1,642684,16⟩
private theorem pass3011_2390 : (Triangular src3011) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3011_2391 : (Triangular src3011) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3011_2393 : (Triangular src3011) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3011_2398 : (Triangular src3011) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3011_2412 : (Triangular src3011) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3011_2449 : (Triangular src3011) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3011 : Cover (Triangular src3011) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3011_2390, by decide, by decide, pass3011_2391, by decide, by decide, pass3011_2393, by decide, by decide, pass3011_2398, by decide, by decide, pass3011_2412, by decide, by decide, pass3011_2449, rfl⟩
def src3012 : Request := ⟨⟨⟨2600,3625,798,50533⟩,535425056505856,4803689494279⟩,85,5,1,642684,16⟩
private theorem pass3012_2390 : (Triangular src3012) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3012_2391 : (Triangular src3012) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3012_2393 : (Triangular src3012) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3012_2398 : (Triangular src3012) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3012_2411 : (Triangular src3012) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3012_2445 : (Triangular src3012) 2445 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3012 : Cover (Triangular src3012) 2534 2390 [2390,2392,2397,2410,2444,2534] := by
  exact ⟨by decide, by decide, pass3012_2390, by decide, by decide, pass3012_2391, by decide, by decide, pass3012_2393, by decide, by decide, pass3012_2398, by decide, by decide, pass3012_2411, by decide, by decide, pass3012_2445, rfl⟩
def src3013 : Request := ⟨⟨⟨5700,7950,1750,73417⟩,5637370734182400,110980791054694⟩,145,5,1,642684,16⟩
private theorem pass3013_2390 : (Triangular src3013) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3013_2391 : (Triangular src3013) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3013_2393 : (Triangular src3013) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3013_2398 : (Triangular src3013) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3013_2411 : (Triangular src3013) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3013_2445 : (Triangular src3013) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3013_2533 : (Triangular src3013) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3013 : Cover (Triangular src3013) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3013_2390, by decide, by decide, pass3013_2391, by decide, by decide, pass3013_2393, by decide, by decide, pass3013_2398, by decide, by decide, pass3013_2411, by decide, by decide, pass3013_2445, by decide, by decide, pass3013_2533, rfl⟩
def src3014 : Request := ⟨⟨⟨4800,6692,1474,130391⟩,3367547627110400,55757027345056⟩,190,5,1,642684,16⟩
private theorem pass3014_2390 : (Triangular src3014) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3014_2391 : (Triangular src3014) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3014_2393 : (Triangular src3014) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3014_2398 : (Triangular src3014) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3014_2411 : (Triangular src3014) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3014_2445 : (Triangular src3014) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3014_2533 : (Triangular src3014) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3014 : Cover (Triangular src3014) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3014_2390, by decide, by decide, pass3014_2391, by decide, by decide, pass3014_2393, by decide, by decide, pass3014_2398, by decide, by decide, pass3014_2411, by decide, by decide, pass3014_2445, by decide, by decide, pass3014_2533, rfl⟩
def src3015 : Request := ⟨⟨⟨10000,13948,3070,121502⟩,30428373265940480,1050983571587703⟩,245,5,1,642684,16⟩
private theorem pass3015_2390 : (Triangular src3015) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3015_2391 : (Triangular src3015) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3015_2393 : (Triangular src3015) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3015_2398 : (Triangular src3015) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3015_2411 : (Triangular src3015) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3015_2444 : (Triangular src3015) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3015_2529 : (Triangular src3015) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3015 : Cover (Triangular src3015) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3015_2390, by decide, by decide, pass3015_2391, by decide, by decide, pass3015_2393, by decide, by decide, pass3015_2398, by decide, by decide, pass3015_2411, by decide, by decide, pass3015_2444, by decide, by decide, pass3015_2529, rfl⟩
def src3016 : Request := ⟨⟨⟨325,453,100,3389⟩,1061047500800,1193036697⟩,0,5,1,642684,26⟩
private theorem pass3016_2390 : (Triangular src3016) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3016_2391 : (Triangular src3016) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3016_2394 : (Triangular src3016) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3016_2403 : (Triangular src3016) 2403 2432 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3016_2433 : (Triangular src3016) 2433 2529 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3016_2530 : (Triangular src3016) 2530 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3016 : Cover (Triangular src3016) 2534 2390 [2390,2393,2402,2432,2529,2534] := by
  exact ⟨by decide, by decide, pass3016_2390, by decide, by decide, pass3016_2391, by decide, by decide, pass3016_2394, by decide, by decide, pass3016_2403, by decide, by decide, pass3016_2433, by decide, by decide, pass3016_2530, rfl⟩
def src3017 : Request := ⟨⟨⟨400,558,123,3762⟩,1971918995456,2734096379⟩,1,5,1,642684,26⟩
private theorem pass3017_2390 : (Triangular src3017) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3017_2391 : (Triangular src3017) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3017_2394 : (Triangular src3017) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3017_2403 : (Triangular src3017) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3017_2431 : (Triangular src3017) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3017_2517 : (Triangular src3017) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3017 : Cover (Triangular src3017) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass3017_2390, by decide, by decide, pass3017_2391, by decide, by decide, pass3017_2394, by decide, by decide, pass3017_2403, by decide, by decide, pass3017_2431, by decide, by decide, pass3017_2517, rfl⟩
def src3018 : Request := ⟨⟨⟨470,655,141,4617⟩,3134317133824,5085275599⟩,3,5,1,642684,26⟩
private theorem pass3018_2390 : (Triangular src3018) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3018_2391 : (Triangular src3018) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3018_2394 : (Triangular src3018) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3018_2403 : (Triangular src3018) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3018_2430 : (Triangular src3018) 2430 2511 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3018_2512 : (Triangular src3018) 2512 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3018 : Cover (Triangular src3018) 2534 2390 [2390,2393,2402,2429,2511,2534] := by
  exact ⟨by decide, by decide, pass3018_2390, by decide, by decide, pass3018_2391, by decide, by decide, pass3018_2394, by decide, by decide, pass3018_2403, by decide, by decide, pass3018_2430, by decide, by decide, pass3018_2512, rfl⟩
def src3019 : Request := ⟨⟨⟨560,781,172,5438⟩,5388141854720,10440670587⟩,6,5,1,642684,26⟩
private theorem pass3019_2390 : (Triangular src3019) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3019_2391 : (Triangular src3019) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3019_2393 : (Triangular src3019) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3019_2399 : (Triangular src3019) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3019_2417 : (Triangular src3019) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3019_2469 : (Triangular src3019) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3019 : Cover (Triangular src3019) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3019_2390, by decide, by decide, pass3019_2391, by decide, by decide, pass3019_2393, by decide, by decide, pass3019_2399, by decide, by decide, pass3019_2417, by decide, by decide, pass3019_2469, rfl⟩
def src3020 : Request := ⟨⟨⟨825,1151,253,7861⟩,17161575202816,49010625289⟩,13,5,1,642684,26⟩
private theorem pass3020_2390 : (Triangular src3020) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3020_2391 : (Triangular src3020) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3020_2393 : (Triangular src3020) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3020_2399 : (Triangular src3020) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3020_2416 : (Triangular src3020) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3020_2463 : (Triangular src3020) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3020 : Cover (Triangular src3020) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass3020_2390, by decide, by decide, pass3020_2391, by decide, by decide, pass3020_2393, by decide, by decide, pass3020_2399, by decide, by decide, pass3020_2416, by decide, by decide, pass3020_2463, rfl⟩
def src3021 : Request := ⟨⟨⟨1450,2022,445,14231⟩,92998964346880,465769321795⟩,32,5,1,642684,26⟩
private theorem pass3021_2390 : (Triangular src3021) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3021_2391 : (Triangular src3021) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3021_2393 : (Triangular src3021) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3021_2399 : (Triangular src3021) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3021_2415 : (Triangular src3021) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3021_2458 : (Triangular src3021) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3021 : Cover (Triangular src3021) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3021_2390, by decide, by decide, pass3021_2391, by decide, by decide, pass3021_2393, by decide, by decide, pass3021_2399, by decide, by decide, pass3021_2415, by decide, by decide, pass3021_2458, rfl⟩
def src3022 : Request := ⟨⟨⟨3200,4463,982,32168⟩,997767489781760,11028049925768⟩,85,5,1,642684,26⟩
private theorem pass3022_2390 : (Triangular src3022) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3022_2391 : (Triangular src3022) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3022_2393 : (Triangular src3022) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3022_2398 : (Triangular src3022) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3022_2411 : (Triangular src3022) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3022_2445 : (Triangular src3022) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3022_2534 : (Triangular src3022) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3022 : Cover (Triangular src3022) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3022_2390, by decide, by decide, pass3022_2391, by decide, by decide, pass3022_2393, by decide, by decide, pass3022_2398, by decide, by decide, pass3022_2411, by decide, by decide, pass3022_2445, by decide, by decide, pass3022_2534, rfl⟩
def src3023 : Request := ⟨⟨⟨3200,4462,982,44420⟩,997767489781760,11020095796464⟩,110,5,1,642684,26⟩
private theorem pass3023_2390 : (Triangular src3023) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3023_2391 : (Triangular src3023) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3023_2393 : (Triangular src3023) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3023_2398 : (Triangular src3023) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3023_2411 : (Triangular src3023) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3023_2445 : (Triangular src3023) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3023_2534 : (Triangular src3023) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3023 : Cover (Triangular src3023) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3023_2390, by decide, by decide, pass3023_2391, by decide, by decide, pass3023_2393, by decide, by decide, pass3023_2398, by decide, by decide, pass3023_2411, by decide, by decide, pass3023_2445, by decide, by decide, pass3023_2534, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2114

-- Source: Research6969.PrefixRescueDataMiddle11
section Z6969Source2115
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle11
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,25⟩
  bank i := ![bank134 4812, bank141 5549, bank141 5956, bank155 6902, bank193 8565, bank222 12404, bank242 23768, bank262 50533, bank338 73417, bank319 130391, bank375 121502] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 85, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 16

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 4812
    · exact rank141 5549
    · exact rank141 5956
    · exact rank155 6902
    · exact rank193 8565
    · exact rank222 12404
    · exact rank242 23768
    · exact rank262 50533
    · exact rank338 73417
    · exact rank319 130391
    · exact rank375 121502
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3005⟩
    · exact ⟨_, cover3006⟩
    · exact ⟨_, cover3007⟩
    · exact ⟨_, cover3008⟩
    · exact ⟨_, cover3009⟩
    · exact ⟨_, cover3010⟩
    · exact ⟨_, cover3011⟩
    · exact ⟨_, cover3012⟩
    · exact ⟨_, cover3013⟩
    · exact ⟨_, cover3014⟩
    · exact ⟨_, cover3015⟩

def price : EarlyPrice := ⟨5, 25, 10, 80/100, 70/100, ![1270386082727, 295389056306, 29910693790, 4785730900], 948679882900604⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![12588/191, 117167/146, 565835/146, 1518775/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle11
end Z6969Source2115

-- Source: Research6969.PrefixMiddleSaved11
section Z6969Source2116
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved11
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle11.price Lower6960.Prefix6969RescueData.Middle11.price :=
  ⟨342, 3707, 65, 802, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle11.plan Lower6960.Prefix6969RescueData.Middle11.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 5 16 25 :=
  ⟨Lower6960.Prefix6969MainCases.Middle11.plan, Lower6960.Prefix6969MainCases.Middle11.price, Lower6960.Prefix6969MainCases.Middle11.valid, Lower6960.Prefix6969MainCases.Middle11.priced, Lower6960.Prefix6969MainCases.Middle11.sources,
   Lower6960.Prefix6969RescueData.Middle11.plan, Lower6960.Prefix6969RescueData.Middle11.price, Lower6960.Prefix6969RescueData.Middle11.sources, Lower6960.Prefix6969RescueData.Middle11.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved11
end Z6969Source2116

-- Source: Research6969.PrefixMainDataMiddle27
section Z6969Source2117
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle27
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 20, 23, 30, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank112 2964, bank92 3992, bank168 3916, bank129 10859, bank161 5142, bank199 7608, bank181 21723, bank212 8810, bank170 28384] i
  head := src3132
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15718, 123771, 573032, 1950355],
    ![25417/2, 90589, 411355, 1399489],
    ![54680/9, 43830, 411355, 1399489],
    ![29433/8, 213037/8, 1929340/9, 679848],
    ![64334/25, 458296/25, 158046, 2223081/4],
    ![17323/9, 13668, 1107215/8, 3458073/8],
    ![18775/16, 276925/32, 2503082/25, 8053584/25],
    ![89110/121, 648600/121, 420040/7, 1337906/7],
    ![89110/121, 648600/121, 116003/2, 1337906/7],
    ![308092/441, 1992668/441, 187473/4, 549081/4],
    ![21715/32, 1992668/441, 187473/4, 549081/4],
    ![21715/32, 1992668/441, 187473/4, 126736],
    ![33263/82, 1992668/441, 187473/4, 126736],
    ![33263/82, 6582024/1681, 3699685/98, 2937796/25],
    ![33263/82, 1603100/441, 16255707/484, 198933984/1849],
    ![474397/1369, 1603100/441, 16255707/484, 198933984/1849],
    ![474397/1369, 9619561/2738, 5616375/169, 77616100/729],
    ![920087/2738, 9619561/2738, 5616375/169, 77616100/729]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 26 642684 := by
  refine ⟨?_, rank154 4358, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3132⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free112_1
    · exact free92_1
    · exact free168_1
    · exact free129_1
    · exact free161_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [240424626, 307367631, 307104066, 306257631, 306421857, 307258212, 307333763, 154634755, 154674012, 102741354, 102690242, 62441880, 59185654, 79698389, 85453181, 93049500, 129603014, 229135653], [1528584, 1153885, 1155235, 1159570, 1158729, 1154445, 1154059, 2492524, 2491871, 3843124, 3845283, 6453513, 6820117, 5012160, 4663232, 4266183, 3001149, 1621500],
  ![121629787325460, 1613206114452, 206222087700, 5549246080], 130320238023791467⟩

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
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 9619561/2738, 5616375/169, 77616100/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle27
end Z6969Source2117

-- Source: Research6969.PrefixRescueDataMiddle27
section Z6969Source2118
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle27
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,40⟩
  bank i := ![bank101 3389, bank134 3762, bank141 4617, bank156 5438, bank204 7861, bank233 14231, bank297 32168, bank296 44420, bank352 66602, bank319 85405, bank307 59170] i
  reserve i := ![0, 1, 3, 6, 13, 32, 85, 110, 190, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 26

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 3389
    · exact rank134 3762
    · exact rank141 4617
    · exact rank156 5438
    · exact rank204 7861
    · exact rank233 14231
    · exact rank297 32168
    · exact rank296 44420
    · exact rank352 66602
    · exact rank319 85405
    · exact rank307 59170
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3016⟩
    · exact ⟨_, cover3017⟩
    · exact ⟨_, cover3018⟩
    · exact ⟨_, cover3019⟩
    · exact ⟨_, cover3020⟩
    · exact ⟨_, cover3021⟩
    · exact ⟨_, cover3022⟩
    · exact ⟨_, cover3023⟩
    · exact ⟨_, cover3026⟩
    · exact ⟨_, cover3025⟩
    · exact ⟨_, cover3024⟩

def price : EarlyPrice := ⟨5, 40, 10, 70/100, 70/100, ![1331347115960, 219943579508, 33889685968, 3388983380], 870441369872358⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![12588/191, 54465/73, 258065/73, 2664080/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle27
end Z6969Source2118

-- Source: Research6969.PrefixMiddleSaved27
section Z6969Source2119
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved27
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle27.price Lower6960.Prefix6969RescueData.Middle27.price :=
  ⟨336, 3513, 65, 746, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle27.plan Lower6960.Prefix6969RescueData.Middle27.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 5 26 40 :=
  ⟨Lower6960.Prefix6969MainCases.Middle27.plan, Lower6960.Prefix6969MainCases.Middle27.price, Lower6960.Prefix6969MainCases.Middle27.valid, Lower6960.Prefix6969MainCases.Middle27.priced, Lower6960.Prefix6969MainCases.Middle27.sources,
   Lower6960.Prefix6969RescueData.Middle27.plan, Lower6960.Prefix6969RescueData.Middle27.price, Lower6960.Prefix6969RescueData.Middle27.sources, Lower6960.Prefix6969RescueData.Middle27.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved27
end Z6969Source2119

end Merged_Z6969Pack0755

-- merged module Z6969Pack0756
section Merged_Z6969Pack0756

-- Source: Research6969.PrefixMainDataMiddle28
section Z6969Source2120
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle28
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 9, 10, 16, 17, 20, 23, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank39 1564, bank46 1778, bank55 1948, bank53 2196, bank74 2799, bank98 2688, bank91 3297, bank138 3222, bank118 3051, bank168 3916, bank131 10228, bank153 5200, bank216 8567, bank183 20877, bank174 26788, bank169 29097] i
  head := src3133
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  historyValues := [![16116, 121824, 560535, 1857143],
    ![25417/2, 171447/2, 397488, 1399489],
    ![54680/9, 373430/9, 397488, 1240610],
    ![29433/8, 25216, 1827296/9, 597792],
    ![64334/25, 433574/25, 158046, 2223081/4],
    ![11819/6, 38762/3, 262533/2, 374578],
    ![2483/2, 131129/16, 95064, 6813296/25],
    ![45497/50, 146976/25, 72563, 1866184/9],
    ![86808/121, 618568/121, 2783600/49, 4822416/25],
    ![86808/121, 618568/121, 2783600/49, 21451536/121],
    ![86808/121, 618568/121, 471110/9, 147456],
    ![258784/441, 1868842/441, 1381443/32, 147456],
    ![258784/441, 1868842/441, 1381443/32, 2315007/16],
    ![258784/441, 1010509/242, 1381443/32, 5845716/49],
    ![258784/441, 1010509/242, 1381443/32, 2813646/25],
    ![688141/1681, 1010509/242, 1381443/32, 2813646/25],
    ![688141/1681, 6203072/1681, 319904/9, 79705600/729],
    ![688141/1681, 9147789/2738, 9143764/289, 73393489/784],
    ![954471/2738, 9147789/2738, 9143764/289, 73393489/784],
    ![462882/1369, 9147789/2738, 9143764/289, 73393489/784],
    ![459151/1369, 9147789/2738, 9143764/289, 73393489/784]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 5 41 642684 := by
  refine ⟨?_, rank154 3832, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3133⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free39_1
    · exact free46_1
    · exact free55_1
    · exact free53_1
    · exact free74_4
    · exact free98_1
    · exact free91_1
    · exact free138_1
    · exact free118_1
    · exact free168_1
    · exact free131_1
    · exact free153_1
    · exact free216_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨50/100, 80/100, [230385510, 291289622, 291209183, 291384821, 291559315, 291749292, 291569748, 220000000, 187029729, 187124563, 147276174, 124283109, 90899666, 124541129, 61809081, 57531987, 85073073, 84469319, 114433491, 100000000, 217479921], [1611213, 1236226, 1236638, 1235739, 1234845, 1233872, 1234791, 1696693, 2029114, 2027969, 2615003, 3147191, 4374711, 3139970, 6518444, 7021932, 4685827, 4721717, 3427834, 3958949, 1717435],
  ![115442691665220, 1625852907264, 195731928900, 5618843230], 120098019035365770⟩

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
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 9147789/2738, 9143764/289, 73393489/784] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle28
end Z6969Source2120

-- Source: Research6969.PrefixRescueDataMiddle28
section Z6969Source2121
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle28
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,56⟩
  bank i := ![bank79 2264, bank101 2500, bank134 2996, bank142 3643, bank156 4531, bank224 9521, bank247 16935, bank307 34502, bank334 60361, bank336 45252, bank307 34502] i
  reserve i := ![0, 1, 3, 6, 10, 32, 65, 145, 237, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 642684
  seedFloor := 41

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank79 2264
    · exact rank101 2500
    · exact rank134 2996
    · exact rank142 3643
    · exact rank156 4531
    · exact rank224 9521
    · exact rank247 16935
    · exact rank307 34502
    · exact rank334 60361
    · exact rank336 45252
    · exact rank307 34502
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3027⟩
    · exact ⟨_, cover3028⟩
    · exact ⟨_, cover3029⟩
    · exact ⟨_, cover3030⟩
    · exact ⟨_, cover3031⟩
    · exact ⟨_, cover3032⟩
    · exact ⟨_, cover3033⟩
    · exact ⟨_, cover3034⟩
    · exact ⟨_, cover3036⟩
    · exact ⟨_, cover3035⟩
    · exact ⟨_, cover3034⟩

def price : EarlyPrice := ⟨5, 56, 10, 60/100, 50/100, ![1317323473963, 227549219615, 38192145250, 2728022500], 800793034551771⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14715/238, 22383/34, 105795/34, 966056/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle28
end Z6969Source2121

-- Source: Research6969.PrefixMiddleSaved28
section Z6969Source2122
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved28
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle28.price Lower6960.Prefix6969RescueData.Middle28.price :=
  ⟨335, 3341, 61, 658, true⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle28.plan Lower6960.Prefix6969RescueData.Middle28.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    exact ⟨by decide, by decide +kernel⟩
  · rw [Budget.extra, Budget.adjust]
    decide +kernel

def data : Case 5 41 56 :=
  ⟨Lower6960.Prefix6969MainCases.Middle28.plan, Lower6960.Prefix6969MainCases.Middle28.price, Lower6960.Prefix6969MainCases.Middle28.valid, Lower6960.Prefix6969MainCases.Middle28.priced, Lower6960.Prefix6969MainCases.Middle28.sources,
   Lower6960.Prefix6969RescueData.Middle28.plan, Lower6960.Prefix6969RescueData.Middle28.price, Lower6960.Prefix6969RescueData.Middle28.sources, Lower6960.Prefix6969RescueData.Middle28.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved28
end Z6969Source2122

-- Source: Research6969.PrefixMiddleSelect5
section Z6969Source2123
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer
set_option maxHeartbeats 8000000

theorem choose5 (j : Fin 56) :
    ∃ l u : ℕ, l≤j.val+1 ∧ j.val+1≤u ∧ Nonempty (Case 5 l u) := by
  fin_cases j
  · exact ⟨1, 1, by decide, by decide, ⟨Saved7.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved8.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved8.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved9.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved9.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved9.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved9.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved9.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved10.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved11.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved27.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved28.data⟩⟩

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source2123

-- Source: Research6969.PhysicalChecks200
section Z6969Source2124
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3200 : Request := ⟨⟨⟨275,383,83,2499⟩,635228389376,603020643⟩,2,7,1,899758,41⟩
private theorem pass3200_2390 : (Triangular src3200) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3200_2391 : (Triangular src3200) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3200_2394 : (Triangular src3200) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3200_2404 : (Triangular src3200) 2404 2438 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3200_2439 : (Triangular src3200) 2439 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3200 : Cover (Triangular src3200) 2534 2390 [2390,2393,2403,2438,2534] := by
  exact ⟨by decide, by decide, pass3200_2390, by decide, by decide, pass3200_2391, by decide, by decide, pass3200_2394, by decide, by decide, pass3200_2404, by decide, by decide, pass3200_2439, rfl⟩
def src3201 : Request := ⟨⟨⟨325,453,98,2931⟩,1045036793856,1174588250⟩,4,7,1,899758,41⟩
private theorem pass3201_2390 : (Triangular src3201) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3201_2391 : (Triangular src3201) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3201_2394 : (Triangular src3201) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3201_2404 : (Triangular src3201) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3201_2436 : (Triangular src3201) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3201 : Cover (Triangular src3201) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3201_2390, by decide, by decide, pass3201_2391, by decide, by decide, pass3201_2394, by decide, by decide, pass3201_2404, by decide, by decide, pass3201_2436, rfl⟩
def src3202 : Request := ⟨⟨⟨400,558,123,3697⟩,1971918995456,2734096379⟩,8,7,1,899758,41⟩
private theorem pass3202_2390 : (Triangular src3202) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3202_2391 : (Triangular src3202) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3202_2394 : (Triangular src3202) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3202_2403 : (Triangular src3202) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3202_2431 : (Triangular src3202) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3202_2517 : (Triangular src3202) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3202 : Cover (Triangular src3202) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass3202_2390, by decide, by decide, pass3202_2391, by decide, by decide, pass3202_2394, by decide, by decide, pass3202_2403, by decide, by decide, pass3202_2431, by decide, by decide, pass3202_2517, rfl⟩
def src3203 : Request := ⟨⟨⟨690,962,212,6110⟩,10065769922560,23997864317⟩,20,7,1,899758,41⟩
private theorem pass3203_2390 : (Triangular src3203) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3203_2391 : (Triangular src3203) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3203_2393 : (Triangular src3203) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3203_2399 : (Triangular src3203) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3203_2416 : (Triangular src3203) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3203_2464 : (Triangular src3203) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3203 : Cover (Triangular src3203) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3203_2390, by decide, by decide, pass3203_2391, by decide, by decide, pass3203_2393, by decide, by decide, pass3203_2399, by decide, by decide, pass3203_2416, by decide, by decide, pass3203_2464, rfl⟩
def src3204 : Request := ⟨⟨⟨1200,1673,378,12583⟩,53798525730816,222977190790⟩,50,7,1,899758,41⟩
private theorem pass3204_2390 : (Triangular src3204) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3204_2391 : (Triangular src3204) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3204_2393 : (Triangular src3204) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3204_2399 : (Triangular src3204) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3204_2415 : (Triangular src3204) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3204_2458 : (Triangular src3204) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3204 : Cover (Triangular src3204) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3204_2390, by decide, by decide, pass3204_2391, by decide, by decide, pass3204_2393, by decide, by decide, pass3204_2399, by decide, by decide, pass3204_2415, by decide, by decide, pass3204_2458, rfl⟩
def src3205 : Request := ⟨⟨⟨3200,4461,982,32563⟩,997767489781760,11012145571636⟩,145,7,1,899758,41⟩
private theorem pass3205_2390 : (Triangular src3205) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3205_2391 : (Triangular src3205) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3205_2393 : (Triangular src3205) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3205_2398 : (Triangular src3205) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3205_2411 : (Triangular src3205) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3205_2445 : (Triangular src3205) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3205_2534 : (Triangular src3205) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3205 : Cover (Triangular src3205) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3205_2390, by decide, by decide, pass3205_2391, by decide, by decide, pass3205_2393, by decide, by decide, pass3205_2398, by decide, by decide, pass3205_2411, by decide, by decide, pass3205_2445, by decide, by decide, pass3205_2534, rfl⟩
def src3206 : Request := ⟨⟨⟨3200,4459,1008,59468⟩,1017717693874176,11221829825062⟩,190,7,1,899758,41⟩
private theorem pass3206_2390 : (Triangular src3206) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3206_2391 : (Triangular src3206) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3206_2393 : (Triangular src3206) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3206_2398 : (Triangular src3206) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3206_2411 : (Triangular src3206) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3206_2445 : (Triangular src3206) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3206_2534 : (Triangular src3206) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3206 : Cover (Triangular src3206) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3206_2390, by decide, by decide, pass3206_2391, by decide, by decide, pass3206_2393, by decide, by decide, pass3206_2398, by decide, by decide, pass3206_2411, by decide, by decide, pass3206_2445, by decide, by decide, pass3206_2534, rfl⟩
def src3207 : Request := ⟨⟨⟨3950,5504,1244,85612⟩,1913299978158080,26038250013848⟩,245,7,1,899758,41⟩
private theorem pass3207_2390 : (Triangular src3207) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3207_2391 : (Triangular src3207) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3207_2393 : (Triangular src3207) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3207_2398 : (Triangular src3207) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3207_2411 : (Triangular src3207) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3207_2445 : (Triangular src3207) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3207_2533 : (Triangular src3207) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3207 : Cover (Triangular src3207) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3207_2390, by decide, by decide, pass3207_2391, by decide, by decide, pass3207_2393, by decide, by decide, pass3207_2398, by decide, by decide, pass3207_2411, by decide, by decide, pass3207_2445, by decide, by decide, pass3207_2533, rfl⟩
def src3208 : Request := ⟨⟨⟨5700,7946,1796,51085⟩,5749327563587584,113058766636997⟩,245,7,1,899758,41⟩
private theorem pass3208_2390 : (Triangular src3208) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3208_2391 : (Triangular src3208) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3208_2393 : (Triangular src3208) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3208_2398 : (Triangular src3208) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3208_2411 : (Triangular src3208) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3208_2445 : (Triangular src3208) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3208_2533 : (Triangular src3208) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3208 : Cover (Triangular src3208) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3208_2390, by decide, by decide, pass3208_2391, by decide, by decide, pass3208_2393, by decide, by decide, pass3208_2398, by decide, by decide, pass3208_2411, by decide, by decide, pass3208_2445, by decide, by decide, pass3208_2533, rfl⟩
def src3209 : Request := ⟨⟨⟨556,772,170,5283⟩,5255817068544,9968090926⟩,10,7,2,899757,2⟩
private theorem pass3209_2390 : (Triangular src3209) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3209_2391 : (Triangular src3209) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3209_2393 : (Triangular src3209) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3209_2399 : (Triangular src3209) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3209_2417 : (Triangular src3209) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3209_2469 : (Triangular src3209) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3209 : Cover (Triangular src3209) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3209_2390, by decide, by decide, pass3209_2391, by decide, by decide, pass3209_2393, by decide, by decide, pass3209_2399, by decide, by decide, pass3209_2417, by decide, by decide, pass3209_2469, rfl⟩
def src3210 : Request := ⟨⟨⟨556,772,170,5236⟩,5255817068544,9968090926⟩,10,7,2,899757,3⟩
private theorem pass3210_2390 : (Triangular src3210) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3210_2391 : (Triangular src3210) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3210_2394 : (Triangular src3210) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3210_2402 : (Triangular src3210) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3210_2426 : (Triangular src3210) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3210_2496 : (Triangular src3210) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3210 : Cover (Triangular src3210) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3210_2390, by decide, by decide, pass3210_2391, by decide, by decide, pass3210_2394, by decide, by decide, pass3210_2402, by decide, by decide, pass3210_2426, by decide, by decide, pass3210_2496, rfl⟩
def src3211 : Request := ⟨⟨⟨556,772,170,5142⟩,5255817068544,9968090926⟩,10,7,2,899757,5⟩
private theorem pass3211_2390 : (Triangular src3211) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3211_2391 : (Triangular src3211) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3211_2394 : (Triangular src3211) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3211_2402 : (Triangular src3211) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3211_2426 : (Triangular src3211) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3211_2496 : (Triangular src3211) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3211 : Cover (Triangular src3211) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3211_2390, by decide, by decide, pass3211_2391, by decide, by decide, pass3211_2394, by decide, by decide, pass3211_2402, by decide, by decide, pass3211_2426, by decide, by decide, pass3211_2496, rfl⟩
def src3212 : Request := ⟨⟨⟨556,772,170,4913⟩,5255817068544,9968090926⟩,10,7,2,899757,10⟩
private theorem pass3212_2390 : (Triangular src3212) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3212_2391 : (Triangular src3212) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3212_2394 : (Triangular src3212) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3212_2402 : (Triangular src3212) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3212_2426 : (Triangular src3212) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3212_2496 : (Triangular src3212) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3212 : Cover (Triangular src3212) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3212_2390, by decide, by decide, pass3212_2391, by decide, by decide, pass3212_2394, by decide, by decide, pass3212_2402, by decide, by decide, pass3212_2426, by decide, by decide, pass3212_2496, rfl⟩
def src3213 : Request := ⟨⟨⟨556,772,170,4612⟩,5255817068544,9968090926⟩,10,7,2,899757,17⟩
private theorem pass3213_2390 : (Triangular src3213) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3213_2391 : (Triangular src3213) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3213_2394 : (Triangular src3213) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3213_2402 : (Triangular src3213) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3213_2426 : (Triangular src3213) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3213_2496 : (Triangular src3213) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3213 : Cover (Triangular src3213) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3213_2390, by decide, by decide, pass3213_2391, by decide, by decide, pass3213_2394, by decide, by decide, pass3213_2402, by decide, by decide, pass3213_2426, by decide, by decide, pass3213_2496, rfl⟩
def src3214 : Request := ⟨⟨⟨556,772,170,4227⟩,5255817068544,9968090926⟩,10,7,2,899757,27⟩
private theorem pass3214_2390 : (Triangular src3214) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3214_2391 : (Triangular src3214) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3214_2394 : (Triangular src3214) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3214_2402 : (Triangular src3214) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3214_2426 : (Triangular src3214) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3214_2496 : (Triangular src3214) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3214 : Cover (Triangular src3214) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3214_2390, by decide, by decide, pass3214_2391, by decide, by decide, pass3214_2394, by decide, by decide, pass3214_2402, by decide, by decide, pass3214_2426, by decide, by decide, pass3214_2496, rfl⟩
def src3215 : Request := ⟨⟨⟨556,772,170,3769⟩,5255817068544,9968090926⟩,10,7,2,899757,42⟩
private theorem pass3215_2390 : (Triangular src3215) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3215_2391 : (Triangular src3215) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3215_2394 : (Triangular src3215) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3215_2402 : (Triangular src3215) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3215_2426 : (Triangular src3215) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3215_2496 : (Triangular src3215) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3215 : Cover (Triangular src3215) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3215_2390, by decide, by decide, pass3215_2391, by decide, by decide, pass3215_2394, by decide, by decide, pass3215_2402, by decide, by decide, pass3215_2426, by decide, by decide, pass3215_2496, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2124

-- Source: Research6969.PrefixMainDataMiddle12
section Z6969Source2125
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle12
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank89 2959, bank123 3043, bank83 3955, bank147 5174, bank158 18445, bank211 8704, bank171 27879] i
  head := src3209
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 127940, 591902, 2134290],
    ![24861/2, 98802, 1802727/4, 3185649/2],
    ![29433/8, 465849/16, 234310, 824148],
    ![17323/9, 179741/12, 2424405/16, 8384121/16],
    ![81680/81, 214120/27, 241121/3, 561759/2],
    ![81680/81, 214120/27, 241121/3, 561759/2],
    ![250508/361, 1978132/361, 8911322/169, 31264794/169],
    ![250508/361, 593893/121, 203881/4, 9259849/64],
    ![254619/484, 593893/121, 771225/16, 9259849/64],
    ![254619/484, 878279/200, 1975937/49, 13667121/98],
    ![480716/1323, 878279/200, 1975937/49, 13667121/98],
    ![480716/1323, 20860364/5329, 22055936/625, 75759616/625],
    ![1826342/5329, 20860364/5329, 22055936/625, 75759616/625]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 1 771221 := by
  refine ⟨?_, rank154 5283, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3209⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free89_3
    · exact free123_1
    · exact free83_3
    · exact free147_1
    · exact free158_1
    · exact free211_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [260269340, 333448103, 332721037, 331689630, 148946676, 148798054, 148733031, 36788937, 69206913, 73668909, 104018099, 88458518, 226537110], [1395092, 1033746, 1035741, 1038570, 2587199, 2589672, 2590755, 11091019, 5802710, 5440419, 3789789, 4497944, 1642888],
  ![120250428730200, 1616025677400, 203883399000, 5549227380], 143167404073387209⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 29 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 20860364/5329, 22055936/625, 75759616/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle12
end Z6969Source2125

-- Source: Research6969.PhysicalChecks191
section Z6969Source2126
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3056 : Request := ⟨⟨⟨1000,1395,307,15341⟩,30557599170560,105715278267⟩,20,6,1,771221,1⟩
private theorem pass3056_2390 : (Triangular src3056) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3056_2391 : (Triangular src3056) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3056_2393 : (Triangular src3056) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3056_2399 : (Triangular src3056) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3056_2415 : (Triangular src3056) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3056_2459 : (Triangular src3056) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3056 : Cover (Triangular src3056) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3056_2390, by decide, by decide, pass3056_2391, by decide, by decide, pass3056_2393, by decide, by decide, pass3056_2399, by decide, by decide, pass3056_2415, by decide, by decide, pass3056_2459, rfl⟩
def src3057 : Request := ⟨⟨⟨1200,1673,368,17962⟩,52718727069696,218387554859⟩,25,6,1,771221,1⟩
private theorem pass3057_2390 : (Triangular src3057) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3057_2391 : (Triangular src3057) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3057_2393 : (Triangular src3057) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3057_2399 : (Triangular src3057) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3057_2415 : (Triangular src3057) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3057_2458 : (Triangular src3057) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3057 : Cover (Triangular src3057) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3057_2390, by decide, by decide, pass3057_2391, by decide, by decide, pass3057_2393, by decide, by decide, pass3057_2399, by decide, by decide, pass3057_2415, by decide, by decide, pass3057_2458, rfl⟩
def src3058 : Request := ⟨⟨⟨1750,2441,537,25782⟩,163381988556800,988269431527⟩,40,6,1,771221,1⟩
private theorem pass3058_2390 : (Triangular src3058) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3058_2391 : (Triangular src3058) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3058_2393 : (Triangular src3058) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3058_2398 : (Triangular src3058) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3058_2412 : (Triangular src3058) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3058_2449 : (Triangular src3058) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3058 : Cover (Triangular src3058) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3058_2390, by decide, by decide, pass3058_2391, by decide, by decide, pass3058_2393, by decide, by decide, pass3058_2398, by decide, by decide, pass3058_2412, by decide, by decide, pass3058_2449, rfl⟩
def src3059 : Request := ⟨⟨⟨4800,6694,1474,78453⟩,3367547627110400,55810706074581⟩,145,6,1,771221,1⟩
private theorem pass3059_2390 : (Triangular src3059) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3059_2391 : (Triangular src3059) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3059_2393 : (Triangular src3059) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3059_2398 : (Triangular src3059) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3059_2411 : (Triangular src3059) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3059_2445 : (Triangular src3059) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3059_2533 : (Triangular src3059) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3059 : Cover (Triangular src3059) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3059_2390, by decide, by decide, pass3059_2391, by decide, by decide, pass3059_2393, by decide, by decide, pass3059_2398, by decide, by decide, pass3059_2411, by decide, by decide, pass3059_2445, by decide, by decide, pass3059_2533, rfl⟩
def src3060 : Request := ⟨⟨⟨8300,11575,2548,129545⟩,17399709518790656,498569901356632⟩,245,6,1,771221,1⟩
private theorem pass3060_2390 : (Triangular src3060) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3060_2391 : (Triangular src3060) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3060_2393 : (Triangular src3060) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3060_2398 : (Triangular src3060) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3060_2411 : (Triangular src3060) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3060_2444 : (Triangular src3060) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3060_2529 : (Triangular src3060) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3060 : Cover (Triangular src3060) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3060_2390, by decide, by decide, pass3060_2391, by decide, by decide, pass3060_2393, by decide, by decide, pass3060_2398, by decide, by decide, pass3060_2411, by decide, by decide, pass3060_2444, by decide, by decide, pass3060_2529, rfl⟩
def src3061 : Request := ⟨⟨⟨325,453,98,5118⟩,1045036793856,1174588250⟩,0,6,1,771221,2⟩
private theorem pass3061_2390 : (Triangular src3061) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3061_2391 : (Triangular src3061) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3061_2394 : (Triangular src3061) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3061_2404 : (Triangular src3061) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3061_2436 : (Triangular src3061) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3061 : Cover (Triangular src3061) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3061_2390, by decide, by decide, pass3061_2391, by decide, by decide, pass3061_2394, by decide, by decide, pass3061_2404, by decide, by decide, pass3061_2436, rfl⟩
def src3062 : Request := ⟨⟨⟨325,453,100,5483⟩,1061047500800,1193036697⟩,1,6,1,771221,2⟩
private theorem pass3062_2390 : (Triangular src3062) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3062_2391 : (Triangular src3062) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3062_2394 : (Triangular src3062) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3062_2403 : (Triangular src3062) 2403 2432 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3062_2433 : (Triangular src3062) 2433 2529 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3062_2530 : (Triangular src3062) 2530 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3062 : Cover (Triangular src3062) 2534 2390 [2390,2393,2402,2432,2529,2534] := by
  exact ⟨by decide, by decide, pass3062_2390, by decide, by decide, pass3062_2391, by decide, by decide, pass3062_2394, by decide, by decide, pass3062_2403, by decide, by decide, pass3062_2433, by decide, by decide, pass3062_2530, rfl⟩
def src3063 : Request := ⟨⟨⟨400,558,123,6487⟩,1971918995456,2734096379⟩,3,6,1,771221,2⟩
private theorem pass3063_2390 : (Triangular src3063) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3063_2391 : (Triangular src3063) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3063_2394 : (Triangular src3063) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3063_2403 : (Triangular src3063) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3063_2430 : (Triangular src3063) 2430 2512 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3063_2513 : (Triangular src3063) 2513 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3063 : Cover (Triangular src3063) 2534 2390 [2390,2393,2402,2429,2512,2534] := by
  exact ⟨by decide, by decide, pass3063_2390, by decide, by decide, pass3063_2391, by decide, by decide, pass3063_2394, by decide, by decide, pass3063_2403, by decide, by decide, pass3063_2430, by decide, by decide, pass3063_2513, rfl⟩
def src3064 : Request := ⟨⟨⟨470,655,144,7989⟩,3184589537280,5168862572⟩,6,6,1,771221,2⟩
private theorem pass3064_2390 : (Triangular src3064) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3064_2391 : (Triangular src3064) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3064_2394 : (Triangular src3064) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3064_2402 : (Triangular src3064) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3064_2426 : (Triangular src3064) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3064_2498 : (Triangular src3064) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3064 : Cover (Triangular src3064) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass3064_2390, by decide, by decide, pass3064_2391, by decide, by decide, pass3064_2394, by decide, by decide, pass3064_2402, by decide, by decide, pass3064_2426, by decide, by decide, pass3064_2498, rfl⟩
def src3065 : Request := ⟨⟨⟨560,781,176,9999⟩,5482316038144,10627925923⟩,10,6,1,771221,2⟩
private theorem pass3065_2390 : (Triangular src3065) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3065_2391 : (Triangular src3065) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3065_2393 : (Triangular src3065) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3065_2399 : (Triangular src3065) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3065_2417 : (Triangular src3065) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3065_2469 : (Triangular src3065) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3065 : Cover (Triangular src3065) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3065_2390, by decide, by decide, pass3065_2391, by decide, by decide, pass3065_2393, by decide, by decide, pass3065_2399, by decide, by decide, pass3065_2417, by decide, by decide, pass3065_2469, rfl⟩
def src3066 : Request := ⟨⟨⟨825,1150,248,13386⟩,16903818182656,48121815022⟩,16,6,1,771221,2⟩
private theorem pass3066_2390 : (Triangular src3066) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3066_2391 : (Triangular src3066) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3066_2393 : (Triangular src3066) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3066_2399 : (Triangular src3066) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3066_2416 : (Triangular src3066) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3066_2464 : (Triangular src3066) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3066 : Cover (Triangular src3066) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3066_2390, by decide, by decide, pass3066_2391, by decide, by decide, pass3066_2393, by decide, by decide, pass3066_2399, by decide, by decide, pass3066_2416, by decide, by decide, pass3066_2464, rfl⟩
def src3067 : Request := ⟨⟨⟨1200,1673,368,17611⟩,52718727069696,218387554859⟩,25,6,1,771221,2⟩
private theorem pass3067_2390 : (Triangular src3067) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3067_2391 : (Triangular src3067) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3067_2393 : (Triangular src3067) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3067_2399 : (Triangular src3067) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3067_2415 : (Triangular src3067) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3067_2458 : (Triangular src3067) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3067 : Cover (Triangular src3067) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3067_2390, by decide, by decide, pass3067_2391, by decide, by decide, pass3067_2393, by decide, by decide, pass3067_2399, by decide, by decide, pass3067_2415, by decide, by decide, pass3067_2458, rfl⟩
def src3068 : Request := ⟨⟨⟨1200,1673,368,41393⟩,52718727069696,218387554859⟩,50,6,1,771221,2⟩
private theorem pass3068_2390 : (Triangular src3068) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3068_2391 : (Triangular src3068) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3068_2393 : (Triangular src3068) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3068_2399 : (Triangular src3068) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3068_2415 : (Triangular src3068) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3068_2458 : (Triangular src3068) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3068 : Cover (Triangular src3068) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3068_2390, by decide, by decide, pass3068_2391, by decide, by decide, pass3068_2393, by decide, by decide, pass3068_2399, by decide, by decide, pass3068_2415, by decide, by decide, pass3068_2458, rfl⟩
def src3069 : Request := ⟨⟨⟨2100,2928,645,37514⟩,282396798484480,2046887686018⟩,65,6,1,771221,2⟩
private theorem pass3069_2390 : (Triangular src3069) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3069_2391 : (Triangular src3069) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3069_2393 : (Triangular src3069) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3069_2398 : (Triangular src3069) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3069_2412 : (Triangular src3069) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3069_2448 : (Triangular src3069) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3069 : Cover (Triangular src3069) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass3069_2390, by decide, by decide, pass3069_2391, by decide, by decide, pass3069_2393, by decide, by decide, pass3069_2398, by decide, by decide, pass3069_2412, by decide, by decide, pass3069_2448, rfl⟩
def src3070 : Request := ⟨⟨⟨4800,6694,1445,79638⟩,3317023033262080,54952917346103⟩,145,6,1,771221,2⟩
private theorem pass3070_2390 : (Triangular src3070) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3070_2391 : (Triangular src3070) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3070_2393 : (Triangular src3070) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3070_2398 : (Triangular src3070) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3070_2411 : (Triangular src3070) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3070_2445 : (Triangular src3070) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3070_2534 : (Triangular src3070) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3070 : Cover (Triangular src3070) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3070_2390, by decide, by decide, pass3070_2391, by decide, by decide, pass3070_2393, by decide, by decide, pass3070_2398, by decide, by decide, pass3070_2411, by decide, by decide, pass3070_2445, by decide, by decide, pass3070_2534, rfl⟩
def src3071 : Request := ⟨⟨⟨8300,11575,2548,127011⟩,17399709518790656,498569901356632⟩,245,6,1,771221,2⟩
private theorem pass3071_2390 : (Triangular src3071) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3071_2391 : (Triangular src3071) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3071_2393 : (Triangular src3071) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3071_2398 : (Triangular src3071) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3071_2411 : (Triangular src3071) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3071_2444 : (Triangular src3071) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3071_2529 : (Triangular src3071) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3071 : Cover (Triangular src3071) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3071_2390, by decide, by decide, pass3071_2391, by decide, by decide, pass3071_2393, by decide, by decide, pass3071_2398, by decide, by decide, pass3071_2411, by decide, by decide, pass3071_2444, by decide, by decide, pass3071_2529, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2126

-- Source: Research6969.PrefixRescueDataMiddle12
section Z6969Source2127
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle12
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,1⟩
  bank i := ![bank101 5097, bank101 5593, bank133 6366, bank141 7411, bank156 9150, bank193 11665, bank222 15341, bank224 17962, bank242 25782, bank322 78453, bank362 129545] i
  reserve i := ![0, 1, 2, 4, 8, 13, 20, 25, 40, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 1

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 5097
    · exact rank101 5593
    · exact rank133 6366
    · exact rank141 7411
    · exact rank156 9150
    · exact rank193 11665
    · exact rank222 15341
    · exact rank224 17962
    · exact rank242 25782
    · exact rank322 78453
    · exact rank362 129545
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3050⟩
    · exact ⟨_, cover3051⟩
    · exact ⟨_, cover3052⟩
    · exact ⟨_, cover3053⟩
    · exact ⟨_, cover3054⟩
    · exact ⟨_, cover3055⟩
    · exact ⟨_, cover3056⟩
    · exact ⟨_, cover3057⟩
    · exact ⟨_, cover3058⟩
    · exact ⟨_, cover3059⟩
    · exact ⟨_, cover3060⟩

def price : EarlyPrice := ⟨6, 1, 10, 95/100, 80/100, ![50486277400, 255947575810, 993006560, 4964997128], 343065707828530⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7032/73, 44031/82, 788845/246, 129545/246] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle12
end Z6969Source2127

-- Source: Research6969.PrefixMiddleSaved12
section Z6969Source2128
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved12
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle12.price Lower6960.Prefix6969RescueData.Middle12.price :=
  ⟨342, 3914, 96, 536, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle12.plan Lower6960.Prefix6969RescueData.Middle12.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 6 1 1 :=
  ⟨Lower6960.Prefix6969MainCases.Middle12.plan, Lower6960.Prefix6969MainCases.Middle12.price, Lower6960.Prefix6969MainCases.Middle12.valid, Lower6960.Prefix6969MainCases.Middle12.priced, Lower6960.Prefix6969MainCases.Middle12.sources,
   Lower6960.Prefix6969RescueData.Middle12.plan, Lower6960.Prefix6969RescueData.Middle12.price, Lower6960.Prefix6969RescueData.Middle12.sources, Lower6960.Prefix6969RescueData.Middle12.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved12
end Z6969Source2128

-- Source: Research6969.PrefixMainDataMiddle13
section Z6969Source2129
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle13
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 15, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1102, bank10 1206, bank24 1404, bank36 1602, bank42 1886, bank52 2212, bank65 2772, bank93 2467, bank83 3955, bank139 4010, bank199 7608, bank158 18445, bank171 27879] i
  head := src3210
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15193, 127451, 590512, 2148349],
    ![24861/2, 98379, 448743, 1578654],
    ![29433/8, 115957/4, 2099672/9, 816816],
    ![34345/18, 133535/9, 606329/4, 1048509/2],
    ![36739/32, 150841/16, 909052/9, 9875096/25],
    ![86036/121, 705908/121, 455636/7, 236368],
    ![86036/121, 705908/121, 455636/7, 236368],
    ![86036/121, 705908/121, 455636/7, 2348584/11],
    ![254619/484, 46036/9, 771225/16, 211310],
    ![254619/484, 356303/75, 6394400/147, 2999480/21],
    ![694280/1323, 584120/147, 4332756/121, 14470416/121],
    ![480716/1323, 584120/147, 4332756/121, 14470416/121],
    ![1826342/5329, 584120/147, 4332756/121, 14470416/121]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 2 771221 := by
  refine ⟨?_, rank154 5236, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3210⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free24_1
    · exact free36_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free93_1
    · exact free83_3
    · exact free139_1
    · exact free199_1
    · exact free158_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [256663090, 329157230, 329090072, 328302980, 329492083, 115460038, 113571836, 58791969, 86878009, 78055947, 94443752, 105891780, 227197779], [1413560, 1045518, 1045703, 1047862, 1044600, 3394100, 3457778, 6865482, 4578534, 5125716, 4195799, 3724675, 1637450],
  ![120601125048780, 1615308715236, 204478001100, 5228230320], 141475487045480902⟩

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
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 584120/147, 4332756/121, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle13
end Z6969Source2129

-- Source: Research6969.PrefixRescueDataMiddle13
section Z6969Source2130
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle13
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,3⟩
  bank i := ![bank100 5118, bank101 5483, bank134 6487, bank142 7989, bank157 9999, bank200 13386, bank224 17611, bank247 37514, bank224 41393, bank321 79638, bank362 127011] i
  reserve i := ![0, 1, 3, 6, 10, 16, 25, 65, 50, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 2

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 5118
    · exact rank101 5483
    · exact rank134 6487
    · exact rank142 7989
    · exact rank157 9999
    · exact rank200 13386
    · exact rank224 17611
    · exact rank247 37514
    · exact rank224 41393
    · exact rank321 79638
    · exact rank362 127011
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3061⟩
    · exact ⟨_, cover3062⟩
    · exact ⟨_, cover3063⟩
    · exact ⟨_, cover3064⟩
    · exact ⟨_, cover3065⟩
    · exact ⟨_, cover3066⟩
    · exact ⟨_, cover3067⟩
    · exact ⟨_, cover3069⟩
    · exact ⟨_, cover3068⟩
    · exact ⟨_, cover3070⟩
    · exact ⟨_, cover3071⟩

def price : EarlyPrice := ⟨6, 3, 10, 95/100, 80/100, ![148495164672, 258045791550, 2978999296, 4964997128], 383503245580920⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![1171/17, 44885/82, 265597/82, 127011/82] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle13
end Z6969Source2130

-- Source: Research6969.PrefixMiddleSaved13
section Z6969Source2131
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved13
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle13.price Lower6960.Prefix6969RescueData.Middle13.price :=
  ⟨342, 3973, 68, 547, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle13.plan Lower6960.Prefix6969RescueData.Middle13.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 6 2 3 :=
  ⟨Lower6960.Prefix6969MainCases.Middle13.plan, Lower6960.Prefix6969MainCases.Middle13.price, Lower6960.Prefix6969MainCases.Middle13.valid, Lower6960.Prefix6969MainCases.Middle13.priced, Lower6960.Prefix6969MainCases.Middle13.sources,
   Lower6960.Prefix6969RescueData.Middle13.plan, Lower6960.Prefix6969RescueData.Middle13.price, Lower6960.Prefix6969RescueData.Middle13.sources, Lower6960.Prefix6969RescueData.Middle13.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved13
end Z6969Source2131

end Merged_Z6969Pack0756

-- merged module Z6969Pack0757
section Merged_Z6969Pack0757

-- Source: Research6969.PrefixMainDataMiddle14
section Z6969Source2132
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle14
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 21, 21, 65, 65, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank108 3149, bank83 3955, bank167 13649, bank199 7608, bank171 27879] i
  head := src3211
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![15589, 127234, 588887, 2113876],
    ![24861/2, 97533, 889731/2, 1550313],
    ![6218, 427742/9, 889731/2, 1550313],
    ![29433/8, 229893/8, 693812/3, 802152],
    ![17323/9, 44336/3, 1196199/8, 4080177/8],
    ![81680/81, 211300/27, 79324, 273383],
    ![81680/81, 211300/27, 79324, 273383],
    ![76938/121, 573674/121, 1520967/32, 9916201/64],
    ![254619/484, 573674/121, 1520967/32, 9916201/64],
    ![55840/147, 573674/121, 22153341/484, 9916201/64],
    ![55840/147, 1736380/441, 4332756/121, 14470416/121],
    ![1826342/5329, 1736380/441, 4332756/121, 14470416/121]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 4 771221 := by
  refine ⟨?_, rank154 5142, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3211⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free108_2
    · exact free83_3
    · exact free167_1
    · exact free199_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [256864296, 327494607, 327459844, 328865926, 328125342, 166871313, 166979956, 155436578, 81836087, 100127842, 116028284, 227078780], [1412530, 1050808, 1050986, 1046318, 1048349, 2288855, 2287046, 2479178, 4878247, 3953547, 3378198, 1638430],
  ![120537957999600, 1615438126120, 204370902000, 4975811940], 141352325055757756⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1736380/441, 4332756/121, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle14
end Z6969Source2132

-- Source: Research6969.PhysicalChecks192
section Z6969Source2133
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3072 : Request := ⟨⟨⟨325,453,98,4917⟩,1045036793856,1174588250⟩,0,6,1,771221,4⟩
private theorem pass3072_2390 : (Triangular src3072) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3072_2391 : (Triangular src3072) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3072_2394 : (Triangular src3072) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3072_2404 : (Triangular src3072) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3072_2436 : (Triangular src3072) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3072 : Cover (Triangular src3072) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3072_2390, by decide, by decide, pass3072_2391, by decide, by decide, pass3072_2394, by decide, by decide, pass3072_2404, by decide, by decide, pass3072_2436, rfl⟩
def src3073 : Request := ⟨⟨⟨325,453,98,5407⟩,1045036793856,1174588250⟩,1,6,1,771221,4⟩
private theorem pass3073_2390 : (Triangular src3073) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3073_2391 : (Triangular src3073) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3073_2394 : (Triangular src3073) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3073_2404 : (Triangular src3073) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3073_2436 : (Triangular src3073) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3073 : Cover (Triangular src3073) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3073_2390, by decide, by decide, pass3073_2391, by decide, by decide, pass3073_2394, by decide, by decide, pass3073_2404, by decide, by decide, pass3073_2436, rfl⟩
def src3074 : Request := ⟨⟨⟨325,453,100,5832⟩,1061047500800,1193036697⟩,2,6,1,771221,4⟩
private theorem pass3074_2390 : (Triangular src3074) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3074_2391 : (Triangular src3074) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3074_2394 : (Triangular src3074) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3074_2404 : (Triangular src3074) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3074_2436 : (Triangular src3074) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3074 : Cover (Triangular src3074) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3074_2390, by decide, by decide, pass3074_2391, by decide, by decide, pass3074_2394, by decide, by decide, pass3074_2404, by decide, by decide, pass3074_2436, rfl⟩
def src3075 : Request := ⟨⟨⟨400,558,123,6741⟩,1971918995456,2734096379⟩,4,6,1,771221,4⟩
private theorem pass3075_2390 : (Triangular src3075) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3075_2391 : (Triangular src3075) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3075_2394 : (Triangular src3075) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3075_2403 : (Triangular src3075) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3075_2430 : (Triangular src3075) 2430 2512 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3075_2513 : (Triangular src3075) 2513 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3075 : Cover (Triangular src3075) 2534 2390 [2390,2393,2402,2429,2512,2534] := by
  exact ⟨by decide, by decide, pass3075_2390, by decide, by decide, pass3075_2391, by decide, by decide, pass3075_2394, by decide, by decide, pass3075_2403, by decide, by decide, pass3075_2430, by decide, by decide, pass3075_2513, rfl⟩
def src3076 : Request := ⟨⟨⟨470,655,144,7672⟩,3184589537280,5168862572⟩,6,6,1,771221,4⟩
private theorem pass3076_2390 : (Triangular src3076) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3076_2391 : (Triangular src3076) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3076_2394 : (Triangular src3076) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3076_2402 : (Triangular src3076) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3076_2426 : (Triangular src3076) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3076_2498 : (Triangular src3076) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3076 : Cover (Triangular src3076) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass3076_2390, by decide, by decide, pass3076_2391, by decide, by decide, pass3076_2394, by decide, by decide, pass3076_2402, by decide, by decide, pass3076_2426, by decide, by decide, pass3076_2498, rfl⟩
def src3077 : Request := ⟨⟨⟨690,962,212,9675⟩,10065769922560,23997864317⟩,10,6,1,771221,4⟩
private theorem pass3077_2390 : (Triangular src3077) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3077_2391 : (Triangular src3077) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3077_2393 : (Triangular src3077) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3077_2399 : (Triangular src3077) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3077_2416 : (Triangular src3077) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3077_2464 : (Triangular src3077) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3077 : Cover (Triangular src3077) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3077_2390, by decide, by decide, pass3077_2391, by decide, by decide, pass3077_2393, by decide, by decide, pass3077_2399, by decide, by decide, pass3077_2416, by decide, by decide, pass3077_2464, rfl⟩
def src3078 : Request := ⟨⟨⟨1000,1395,307,12984⟩,30557599170560,105715278267⟩,16,6,1,771221,4⟩
private theorem pass3078_2390 : (Triangular src3078) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3078_2391 : (Triangular src3078) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3078_2393 : (Triangular src3078) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3078_2399 : (Triangular src3078) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3078_2415 : (Triangular src3078) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3078_2459 : (Triangular src3078) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3078 : Cover (Triangular src3078) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3078_2390, by decide, by decide, pass3078_2391, by decide, by decide, pass3078_2393, by decide, by decide, pass3078_2399, by decide, by decide, pass3078_2415, by decide, by decide, pass3078_2459, rfl⟩
def src3079 : Request := ⟨⟨⟨1450,2022,445,23937⟩,92998964346880,465769321795⟩,40,6,1,771221,4⟩
private theorem pass3079_2390 : (Triangular src3079) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3079_2391 : (Triangular src3079) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3079_2393 : (Triangular src3079) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3079_2399 : (Triangular src3079) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3079_2415 : (Triangular src3079) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3079_2457 : (Triangular src3079) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3079 : Cover (Triangular src3079) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3079_2390, by decide, by decide, pass3079_2391, by decide, by decide, pass3079_2393, by decide, by decide, pass3079_2399, by decide, by decide, pass3079_2415, by decide, by decide, pass3079_2457, rfl⟩
def src3080 : Request := ⟨⟨⟨1450,2021,445,53870⟩,92998964346880,465028319332⟩,65,6,1,771221,4⟩
private theorem pass3080_2390 : (Triangular src3080) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3080_2391 : (Triangular src3080) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3080_2393 : (Triangular src3080) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3080_2399 : (Triangular src3080) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3080_2415 : (Triangular src3080) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3080_2457 : (Triangular src3080) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3080 : Cover (Triangular src3080) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3080_2390, by decide, by decide, pass3080_2391, by decide, by decide, pass3080_2393, by decide, by decide, pass3080_2399, by decide, by decide, pass3080_2415, by decide, by decide, pass3080_2457, rfl⟩
def src3081 : Request := ⟨⟨⟨3200,4463,982,45731⟩,997767489781760,11028049925768⟩,85,6,1,771221,4⟩
private theorem pass3081_2390 : (Triangular src3081) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3081_2391 : (Triangular src3081) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3081_2393 : (Triangular src3081) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3081_2398 : (Triangular src3081) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3081_2411 : (Triangular src3081) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3081_2445 : (Triangular src3081) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3081_2534 : (Triangular src3081) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3081 : Cover (Triangular src3081) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3081_2390, by decide, by decide, pass3081_2391, by decide, by decide, pass3081_2393, by decide, by decide, pass3081_2398, by decide, by decide, pass3081_2411, by decide, by decide, pass3081_2445, by decide, by decide, pass3081_2534, rfl⟩
def src3082 : Request := ⟨⟨⟨5700,7950,1750,76096⟩,5637370734182400,110980791054694⟩,145,6,1,771221,4⟩
private theorem pass3082_2390 : (Triangular src3082) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3082_2391 : (Triangular src3082) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3082_2393 : (Triangular src3082) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3082_2398 : (Triangular src3082) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3082_2411 : (Triangular src3082) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3082_2445 : (Triangular src3082) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3082_2533 : (Triangular src3082) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3082 : Cover (Triangular src3082) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3082_2390, by decide, by decide, pass3082_2391, by decide, by decide, pass3082_2393, by decide, by decide, pass3082_2398, by decide, by decide, pass3082_2411, by decide, by decide, pass3082_2445, by decide, by decide, pass3082_2533, rfl⟩
def src3083 : Request := ⟨⟨⟨325,453,98,4429⟩,1045036793856,1174588250⟩,0,6,1,771221,9⟩
private theorem pass3083_2390 : (Triangular src3083) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3083_2391 : (Triangular src3083) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3083_2394 : (Triangular src3083) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3083_2404 : (Triangular src3083) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3083_2436 : (Triangular src3083) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3083 : Cover (Triangular src3083) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3083_2390, by decide, by decide, pass3083_2391, by decide, by decide, pass3083_2394, by decide, by decide, pass3083_2404, by decide, by decide, pass3083_2436, rfl⟩
def src3084 : Request := ⟨⟨⟨325,453,98,4867⟩,1045036793856,1174588250⟩,1,6,1,771221,9⟩
private theorem pass3084_2390 : (Triangular src3084) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3084_2391 : (Triangular src3084) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3084_2394 : (Triangular src3084) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3084_2404 : (Triangular src3084) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3084_2436 : (Triangular src3084) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3084 : Cover (Triangular src3084) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3084_2390, by decide, by decide, pass3084_2391, by decide, by decide, pass3084_2394, by decide, by decide, pass3084_2404, by decide, by decide, pass3084_2436, rfl⟩
def src3085 : Request := ⟨⟨⟨400,558,123,5606⟩,1971918995456,2734096379⟩,3,6,1,771221,9⟩
private theorem pass3085_2390 : (Triangular src3085) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3085_2391 : (Triangular src3085) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3085_2394 : (Triangular src3085) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3085_2403 : (Triangular src3085) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3085_2431 : (Triangular src3085) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3085_2517 : (Triangular src3085) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3085 : Cover (Triangular src3085) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass3085_2390, by decide, by decide, pass3085_2391, by decide, by decide, pass3085_2394, by decide, by decide, pass3085_2403, by decide, by decide, pass3085_2431, by decide, by decide, pass3085_2517, rfl⟩
def src3086 : Request := ⟨⟨⟨470,655,144,6901⟩,3184589537280,5168862572⟩,6,6,1,771221,9⟩
private theorem pass3086_2390 : (Triangular src3086) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3086_2391 : (Triangular src3086) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3086_2394 : (Triangular src3086) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3086_2402 : (Triangular src3086) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3086_2426 : (Triangular src3086) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3086_2498 : (Triangular src3086) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3086 : Cover (Triangular src3086) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass3086_2390, by decide, by decide, pass3086_2391, by decide, by decide, pass3086_2394, by decide, by decide, pass3086_2402, by decide, by decide, pass3086_2426, by decide, by decide, pass3086_2498, rfl⟩
def src3087 : Request := ⟨⟨⟨560,781,172,8679⟩,5388141854720,10440670587⟩,10,6,1,771221,9⟩
private theorem pass3087_2390 : (Triangular src3087) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3087_2391 : (Triangular src3087) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3087_2393 : (Triangular src3087) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3087_2399 : (Triangular src3087) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3087_2417 : (Triangular src3087) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3087_2469 : (Triangular src3087) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3087 : Cover (Triangular src3087) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3087_2390, by decide, by decide, pass3087_2391, by decide, by decide, pass3087_2393, by decide, by decide, pass3087_2399, by decide, by decide, pass3087_2417, by decide, by decide, pass3087_2469, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2133

-- Source: Research6969.PrefixRescueDataMiddle14
section Z6969Source2134
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle14
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,8⟩
  bank i := ![bank100 4917, bank100 5407, bank101 5832, bank134 6741, bank142 7672, bank193 9675, bank222 12984, bank233 23937, bank297 45731, bank231 53870, bank338 76096] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 40, 85, 65, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 4

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 4917
    · exact rank100 5407
    · exact rank101 5832
    · exact rank134 6741
    · exact rank142 7672
    · exact rank193 9675
    · exact rank222 12984
    · exact rank233 23937
    · exact rank297 45731
    · exact rank231 53870
    · exact rank338 76096
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3072⟩
    · exact ⟨_, cover3073⟩
    · exact ⟨_, cover3074⟩
    · exact ⟨_, cover3075⟩
    · exact ⟨_, cover3076⟩
    · exact ⟨_, cover3077⟩
    · exact ⟨_, cover3078⟩
    · exact ⟨_, cover3079⟩
    · exact ⟨_, cover3081⟩
    · exact ⟨_, cover3080⟩
    · exact ⟨_, cover3082⟩

def price : EarlyPrice := ⟨6, 8, 10, 90/100, 80/100, ![237246782080, 167609526256, 5456027500, 3410025500], 396985103520467⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![193/3, 45048/73, 260088/73, 304384/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle14
end Z6969Source2134

-- Source: Research6969.PrefixMiddleSaved14
section Z6969Source2135
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved14
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle14.price Lower6960.Prefix6969RescueData.Middle14.price :=
  ⟨342, 3937, 64, 617, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle14.plan Lower6960.Prefix6969RescueData.Middle14.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 6 4 8 :=
  ⟨Lower6960.Prefix6969MainCases.Middle14.plan, Lower6960.Prefix6969MainCases.Middle14.price, Lower6960.Prefix6969MainCases.Middle14.valid, Lower6960.Prefix6969MainCases.Middle14.priced, Lower6960.Prefix6969MainCases.Middle14.sources,
   Lower6960.Prefix6969RescueData.Middle14.plan, Lower6960.Prefix6969RescueData.Middle14.price, Lower6960.Prefix6969RescueData.Middle14.sources, Lower6960.Prefix6969RescueData.Middle14.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved14
end Z6969Source2135

-- Source: Research6969.PrefixMainDataMiddle15
section Z6969Source2136
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle15
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank28 1523, bank37 1587, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank122 10626, bank159 5020, bank199 7608, bank158 18445, bank230 11634, bank172 23613, bank171 27879] i
  head := src3212
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 125248, 579441, 2110860],
    ![24861/2, 95472, 1741677/4, 2962539/2],
    ![6218, 139451/3, 1741677/4, 2962539/2],
    ![29433/8, 449939/16, 2037010/9, 766428],
    ![62542/25, 484908/25, 312215/2, 2319529/4],
    ![17323/9, 57817/4, 2340415/16, 7796931/16],
    ![36739/32, 292961/32, 909052/9, 9265918/25],
    ![86036/121, 685559/121, 3098043/49, 1552508/7],
    ![86036/121, 685559/121, 3098043/49, 1552508/7],
    ![254619/484, 2199562/441, 771225/16, 2775845/14],
    ![254619/484, 2199562/441, 771225/16, 2775845/14],
    ![254619/484, 571693/121, 771225/16, 9259849/64],
    ![41249/100, 571693/121, 771225/16, 9259849/64],
    ![41249/100, 68527/16, 1960310/49, 6300100/49],
    ![41249/100, 1697450/441, 34407849/968, 14016789/121],
    ![480716/1323, 1697450/441, 34407849/968, 14016789/121],
    ![480716/1323, 1146695/306, 29290475/864, 2762244/25],
    ![1872696/5329, 1146695/306, 29290475/864, 2762244/25],
    ![1826342/5329, 1146695/306, 29290475/864, 2762244/25]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 9 771221 := by
  refine ⟨?_, rank154 4913, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3212⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free28_1
    · exact free37_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free122_1
    · exact free159_1
    · exact free199_1
    · exact free158_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [247574701, 317578016, 316838168, 316974592, 316355098, 316779987, 317322018, 146948332, 147088938, 147177836, 146986348, 69950410, 69987922, 68435804, 79582066, 124211412, 100670807, 100000000, 224738620], [1469733, 1101594, 1105383, 1104685, 1107857, 1105681, 1102905, 2620460, 2618119, 2616640, 2619827, 5736277, 5733292, 5872666, 5020203, 3149197, 3930606, 3958949, 1657691],
  ![119295754268400, 1617977164700, 211159400400, 5990119320], 135170501278623260⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1146695/306, 29290475/864, 2762244/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle15
end Z6969Source2136

-- Source: Research6969.PhysicalChecks193
section Z6969Source2137
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3088 : Request := ⟨⟨⟨1000,1395,301,13432⟩,30103476895744,104105680031⟩,20,6,1,771221,9⟩
private theorem pass3088_2390 : (Triangular src3088) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3088_2391 : (Triangular src3088) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3088_2393 : (Triangular src3088) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3088_2399 : (Triangular src3088) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3088_2415 : (Triangular src3088) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3088_2459 : (Triangular src3088) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3088 : Cover (Triangular src3088) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3088_2390, by decide, by decide, pass3088_2391, by decide, by decide, pass3088_2393, by decide, by decide, pass3088_2399, by decide, by decide, pass3088_2415, by decide, by decide, pass3088_2459, rfl⟩
def src3089 : Request := ⟨⟨⟨1450,2022,457,21321⟩,94890063298560,475487789910⟩,40,6,1,771221,9⟩
private theorem pass3089_2390 : (Triangular src3089) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3089_2391 : (Triangular src3089) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3089_2393 : (Triangular src3089) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3089_2399 : (Triangular src3089) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3089_2415 : (Triangular src3089) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3089_2457 : (Triangular src3089) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3089 : Cover (Triangular src3089) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3089_2390, by decide, by decide, pass3089_2391, by decide, by decide, pass3089_2393, by decide, by decide, pass3089_2399, by decide, by decide, pass3089_2415, by decide, by decide, pass3089_2457, rfl⟩
def src3090 : Request := ⟨⟨⟨1200,1673,378,35081⟩,53798525730816,222977190790⟩,50,6,1,771221,9⟩
private theorem pass3090_2390 : (Triangular src3090) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3090_2391 : (Triangular src3090) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3090_2393 : (Triangular src3090) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3090_2399 : (Triangular src3090) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3090_2415 : (Triangular src3090) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3090_2458 : (Triangular src3090) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3090 : Cover (Triangular src3090) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3090_2390, by decide, by decide, pass3090_2391, by decide, by decide, pass3090_2393, by decide, by decide, pass3090_2399, by decide, by decide, pass3090_2415, by decide, by decide, pass3090_2458, rfl⟩
def src3091 : Request := ⟨⟨⟨3200,4463,982,41180⟩,997767489781760,11028049925768⟩,85,6,1,771221,9⟩
private theorem pass3091_2390 : (Triangular src3091) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3091_2391 : (Triangular src3091) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3091_2393 : (Triangular src3091) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3091_2398 : (Triangular src3091) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3091_2411 : (Triangular src3091) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3091_2445 : (Triangular src3091) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3091_2534 : (Triangular src3091) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3091 : Cover (Triangular src3091) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3091_2390, by decide, by decide, pass3091_2391, by decide, by decide, pass3091_2393, by decide, by decide, pass3091_2398, by decide, by decide, pass3091_2411, by decide, by decide, pass3091_2445, by decide, by decide, pass3091_2534, rfl⟩
def src3092 : Request := ⟨⟨⟨5700,7950,1796,67845⟩,5749327563587584,113242283843565⟩,145,6,1,771221,9⟩
private theorem pass3092_2390 : (Triangular src3092) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3092_2391 : (Triangular src3092) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3092_2393 : (Triangular src3092) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3092_2398 : (Triangular src3092) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3092_2411 : (Triangular src3092) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3092_2445 : (Triangular src3092) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3092_2532 : (Triangular src3092) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3092 : Cover (Triangular src3092) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3092_2390, by decide, by decide, pass3092_2391, by decide, by decide, pass3092_2393, by decide, by decide, pass3092_2398, by decide, by decide, pass3092_2411, by decide, by decide, pass3092_2445, by decide, by decide, pass3092_2532, rfl⟩
def src3093 : Request := ⟨⟨⟨4800,6690,1512,173646⟩,3433136573644800,56816483122989⟩,245,6,1,771221,9⟩
private theorem pass3093_2390 : (Triangular src3093) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3093_2391 : (Triangular src3093) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3093_2393 : (Triangular src3093) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3093_2398 : (Triangular src3093) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3093_2411 : (Triangular src3093) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3093_2445 : (Triangular src3093) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3093_2532 : (Triangular src3093) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3093 : Cover (Triangular src3093) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3093_2390, by decide, by decide, pass3093_2391, by decide, by decide, pass3093_2393, by decide, by decide, pass3093_2398, by decide, by decide, pass3093_2411, by decide, by decide, pass3093_2445, by decide, by decide, pass3093_2532, rfl⟩
def src3094 : Request := ⟨⟨⟨325,453,100,3691⟩,1061047500800,1193036697⟩,0,6,1,771221,16⟩
private theorem pass3094_2390 : (Triangular src3094) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3094_2391 : (Triangular src3094) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3094_2394 : (Triangular src3094) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3094_2404 : (Triangular src3094) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3094_2436 : (Triangular src3094) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3094 : Cover (Triangular src3094) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3094_2390, by decide, by decide, pass3094_2391, by decide, by decide, pass3094_2394, by decide, by decide, pass3094_2404, by decide, by decide, pass3094_2436, rfl⟩
def src3095 : Request := ⟨⟨⟨400,558,120,4635⟩,1935519252480,2682384904⟩,2,6,1,771221,16⟩
private theorem pass3095_2390 : (Triangular src3095) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3095_2391 : (Triangular src3095) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3095_2394 : (Triangular src3095) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3095_2403 : (Triangular src3095) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3095_2431 : (Triangular src3095) 2431 2517 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3095_2518 : (Triangular src3095) 2518 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3095 : Cover (Triangular src3095) 2534 2390 [2390,2393,2402,2430,2517,2534] := by
  exact ⟨by decide, by decide, pass3095_2390, by decide, by decide, pass3095_2391, by decide, by decide, pass3095_2394, by decide, by decide, pass3095_2403, by decide, by decide, pass3095_2431, by decide, by decide, pass3095_2518, rfl⟩
def src3096 : Request := ⟨⟨⟨470,655,144,5204⟩,3184589537280,5168862572⟩,4,6,1,771221,16⟩
private theorem pass3096_2390 : (Triangular src3096) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3096_2391 : (Triangular src3096) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3096_2394 : (Triangular src3096) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3096_2402 : (Triangular src3096) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3096_2426 : (Triangular src3096) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3096_2498 : (Triangular src3096) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3096 : Cover (Triangular src3096) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass3096_2390, by decide, by decide, pass3096_2391, by decide, by decide, pass3096_2394, by decide, by decide, pass3096_2402, by decide, by decide, pass3096_2426, by decide, by decide, pass3096_2498, rfl⟩
def src3097 : Request := ⟨⟨⟨560,781,172,6628⟩,5388141854720,10440670587⟩,8,6,1,771221,16⟩
private theorem pass3097_2390 : (Triangular src3097) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3097_2391 : (Triangular src3097) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3097_2393 : (Triangular src3097) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3097_2399 : (Triangular src3097) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3097_2417 : (Triangular src3097) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3097_2469 : (Triangular src3097) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3097 : Cover (Triangular src3097) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3097_2390, by decide, by decide, pass3097_2391, by decide, by decide, pass3097_2393, by decide, by decide, pass3097_2399, by decide, by decide, pass3097_2417, by decide, by decide, pass3097_2469, rfl⟩
def src3098 : Request := ⟨⟨⟨825,1150,253,11125⟩,17161575202816,48873782027⟩,20,6,1,771221,16⟩
private theorem pass3098_2390 : (Triangular src3098) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3098_2391 : (Triangular src3098) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3098_2393 : (Triangular src3098) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3098_2399 : (Triangular src3098) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3098_2416 : (Triangular src3098) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3098_2463 : (Triangular src3098) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3098 : Cover (Triangular src3098) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass3098_2390, by decide, by decide, pass3098_2391, by decide, by decide, pass3098_2393, by decide, by decide, pass3098_2399, by decide, by decide, pass3098_2416, by decide, by decide, pass3098_2463, rfl⟩
def src3099 : Request := ⟨⟨⟨1450,2022,445,18387⟩,92998964346880,465769321795⟩,40,6,1,771221,16⟩
private theorem pass3099_2390 : (Triangular src3099) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3099_2391 : (Triangular src3099) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3099_2393 : (Triangular src3099) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3099_2399 : (Triangular src3099) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3099_2415 : (Triangular src3099) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3099_2457 : (Triangular src3099) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3099 : Cover (Triangular src3099) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3099_2390, by decide, by decide, pass3099_2391, by decide, by decide, pass3099_2393, by decide, by decide, pass3099_2399, by decide, by decide, pass3099_2415, by decide, by decide, pass3099_2457, rfl⟩
def src3100 : Request := ⟨⟨⟨1450,2021,445,40774⟩,92998964346880,465028319332⟩,65,6,1,771221,16⟩
private theorem pass3100_2390 : (Triangular src3100) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3100_2391 : (Triangular src3100) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3100_2393 : (Triangular src3100) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3100_2399 : (Triangular src3100) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3100_2415 : (Triangular src3100) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3100_2457 : (Triangular src3100) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3100 : Cover (Triangular src3100) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3100_2390, by decide, by decide, pass3100_2391, by decide, by decide, pass3100_2393, by decide, by decide, pass3100_2399, by decide, by decide, pass3100_2415, by decide, by decide, pass3100_2457, rfl⟩
def src3101 : Request := ⟨⟨⟨2600,3625,783,36629⟩,527755772952576,4733203574232⟩,85,6,1,771221,16⟩
private theorem pass3101_2390 : (Triangular src3101) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3101_2391 : (Triangular src3101) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3101_2393 : (Triangular src3101) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3101_2398 : (Triangular src3101) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3101_2412 : (Triangular src3101) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3101_2449 : (Triangular src3101) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3101 : Cover (Triangular src3101) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3101_2390, by decide, by decide, pass3101_2391, by decide, by decide, pass3101_2393, by decide, by decide, pass3101_2398, by decide, by decide, pass3101_2412, by decide, by decide, pass3101_2449, rfl⟩
def src3102 : Request := ⟨⟨⟨4800,6690,1474,149537⟩,3367547627110400,55703383755931⟩,245,6,1,771221,16⟩
private theorem pass3102_2390 : (Triangular src3102) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3102_2391 : (Triangular src3102) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3102_2393 : (Triangular src3102) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3102_2398 : (Triangular src3102) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3102_2411 : (Triangular src3102) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3102_2445 : (Triangular src3102) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3102_2533 : (Triangular src3102) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3102 : Cover (Triangular src3102) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3102_2390, by decide, by decide, pass3102_2391, by decide, by decide, pass3102_2393, by decide, by decide, pass3102_2398, by decide, by decide, pass3102_2411, by decide, by decide, pass3102_2445, by decide, by decide, pass3102_2533, rfl⟩
def src3103 : Request := ⟨⟨⟨6900,9621,2118,94697⟩,9997036108906496,238016971510476⟩,245,6,1,771221,16⟩
private theorem pass3103_2390 : (Triangular src3103) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3103_2391 : (Triangular src3103) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3103_2393 : (Triangular src3103) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3103_2398 : (Triangular src3103) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3103_2411 : (Triangular src3103) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3103_2445 : (Triangular src3103) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3103_2532 : (Triangular src3103) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3103 : Cover (Triangular src3103) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3103_2390, by decide, by decide, pass3103_2391, by decide, by decide, pass3103_2393, by decide, by decide, pass3103_2398, by decide, by decide, pass3103_2411, by decide, by decide, pass3103_2445, by decide, by decide, pass3103_2532, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2137

-- Source: Research6969.PrefixRescueDataMiddle15
section Z6969Source2138
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle15
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,15⟩
  bank i := ![bank100 4429, bank100 4867, bank134 5606, bank142 6901, bank156 8679, bank221 13432, bank234 21321, bank225 35081, bank297 41180, bank339 67845, bank318 173646] i
  reserve i := ![0, 1, 3, 6, 10, 20, 40, 50, 85, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 9

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 4429
    · exact rank100 4867
    · exact rank134 5606
    · exact rank142 6901
    · exact rank156 8679
    · exact rank221 13432
    · exact rank234 21321
    · exact rank225 35081
    · exact rank297 41180
    · exact rank339 67845
    · exact rank318 173646
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3083⟩
    · exact ⟨_, cover3084⟩
    · exact ⟨_, cover3085⟩
    · exact ⟨_, cover3086⟩
    · exact ⟨_, cover3087⟩
    · exact ⟨_, cover3088⟩
    · exact ⟨_, cover3089⟩
    · exact ⟨_, cover3090⟩
    · exact ⟨_, cover3091⟩
    · exact ⟨_, cover3092⟩
    · exact ⟨_, cover3093⟩

def price : EarlyPrice := ⟨6, 15, 10, 85/100, 80/100, ![1015089368040, 368633406276, 10498949040, 3499660456], 641871630714751⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2375/41, 94785/146, 263160/73, 1017675/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle15
end Z6969Source2138

-- Source: Research6969.PrefixMiddleSaved15
section Z6969Source2139
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved15
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle15.price Lower6960.Prefix6969RescueData.Middle15.price :=
  ⟨342, 3747, 57, 649, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle15.plan Lower6960.Prefix6969RescueData.Middle15.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 6 9 15 :=
  ⟨Lower6960.Prefix6969MainCases.Middle15.plan, Lower6960.Prefix6969MainCases.Middle15.price, Lower6960.Prefix6969MainCases.Middle15.valid, Lower6960.Prefix6969MainCases.Middle15.priced, Lower6960.Prefix6969MainCases.Middle15.sources,
   Lower6960.Prefix6969RescueData.Middle15.plan, Lower6960.Prefix6969RescueData.Middle15.price, Lower6960.Prefix6969RescueData.Middle15.sources, Lower6960.Prefix6969RescueData.Middle15.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved15
end Z6969Source2139

-- Source: Research6969.PrefixMainDataMiddle16
section Z6969Source2140
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle16
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 16
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 13, 21, 25, 40, 40, 65, 75, 105, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank33 1472, bank42 1693, bank55 1948, bank72 2320, bank108 3149, bank103 4148, bank124 10359, bank159 5020, bank199 7608, bank187 16602, bank230 11634, bank172 23613, bank171 27879] i
  head := src3213
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15703, 125368, 579801, 2014530],
    ![24861/2, 92763, 423003, 1454436],
    ![6218, 406012/9, 423003, 1454436],
    ![29433/8, 109249/4, 1978616/9, 719472],
    ![65616/25, 471616/25, 158976, 541696],
    ![73478/49, 76694/7, 2418488/25, 2866249/9],
    ![45497/50, 160041/25, 72563, 237169],
    ![45497/50, 160041/25, 1746434/25, 215296],
    ![76938/121, 545054/121, 1520967/32, 7261594/49],
    ![76938/121, 545054/121, 1520967/32, 7261594/49],
    ![20667/50, 545054/121, 1520967/32, 7261594/49],
    ![20667/50, 16605/4, 1960310/49, 92608960/729],
    ![20667/50, 182920/49, 8344833/242, 57881664/529],
    ![1960504/5329, 182920/49, 8344833/242, 57881664/529],
    ![1960504/5329, 556040/153, 5813676/175, 536560080/5041],
    ![1872696/5329, 556040/153, 5813676/175, 536560080/5041],
    ![1826342/5329, 556040/153, 5813676/175, 536560080/5041]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 16 771221 := by
  refine ⟨?_, rank154 4612, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3213⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free33_2
    · exact free42_3
    · exact free55_1
    · exact free72_1
    · exact free108_2
    · exact free103_3
    · exact free124_1
    · exact free159_1
    · exact free199_1
    · exact free187_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [246459942, 314531187, 314435749, 314573787, 315124664, 313078545, 160002366, 159978211, 56282923, 72574561, 72387183, 67238713, 76637417, 119925918, 99052906, 100000000, 223755125], [1478909, 1117198, 1117687, 1116980, 1114159, 1124638, 2403184, 2403586, 7182540, 5527490, 5542398, 5981267, 5223790, 3269124, 3998964, 3958949, 1665786],
  ![118773695452500, 1619044355020, 203874060600, 6216310100], 133252994528015306⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 556040/153, 5813676/175, 536560080/5041] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle16
end Z6969Source2140

-- Source: Research6969.PhysicalChecks194
section Z6969Source2141
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3104 : Request := ⟨⟨⟨8300,11575,2615,92759⟩,17745461310914560,508734991702659⟩,245,6,1,771221,16⟩
private theorem pass3104_2390 : (Triangular src3104) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3104_2391 : (Triangular src3104) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3104_2393 : (Triangular src3104) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3104_2398 : (Triangular src3104) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3104_2411 : (Triangular src3104) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3104_2444 : (Triangular src3104) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3104_2529 : (Triangular src3104) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3104 : Cover (Triangular src3104) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3104_2390, by decide, by decide, pass3104_2391, by decide, by decide, pass3104_2393, by decide, by decide, pass3104_2398, by decide, by decide, pass3104_2411, by decide, by decide, pass3104_2444, by decide, by decide, pass3104_2529, rfl⟩
def src3105 : Request := ⟨⟨⟨275,383,83,2987⟩,635228389376,603020643⟩,0,6,1,771221,26⟩
private theorem pass3105_2390 : (Triangular src3105) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3105_2391 : (Triangular src3105) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3105_2394 : (Triangular src3105) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3105_2404 : (Triangular src3105) 2404 2438 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3105_2439 : (Triangular src3105) 2439 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3105 : Cover (Triangular src3105) 2534 2390 [2390,2393,2403,2438,2534] := by
  exact ⟨by decide, by decide, pass3105_2390, by decide, by decide, pass3105_2391, by decide, by decide, pass3105_2394, by decide, by decide, pass3105_2404, by decide, by decide, pass3105_2439, rfl⟩
def src3106 : Request := ⟨⟨⟨325,453,100,3195⟩,1061047500800,1193036697⟩,1,6,1,771221,26⟩
private theorem pass3106_2390 : (Triangular src3106) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3106_2391 : (Triangular src3106) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3106_2394 : (Triangular src3106) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3106_2403 : (Triangular src3106) 2403 2432 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3106_2433 : (Triangular src3106) 2433 2529 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3106_2530 : (Triangular src3106) 2530 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3106 : Cover (Triangular src3106) 2534 2390 [2390,2393,2402,2432,2529,2534] := by
  exact ⟨by decide, by decide, pass3106_2390, by decide, by decide, pass3106_2391, by decide, by decide, pass3106_2394, by decide, by decide, pass3106_2403, by decide, by decide, pass3106_2433, by decide, by decide, pass3106_2530, rfl⟩
def src3107 : Request := ⟨⟨⟨400,558,120,4267⟩,1935519252480,2682384904⟩,4,6,1,771221,26⟩
private theorem pass3107_2390 : (Triangular src3107) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3107_2391 : (Triangular src3107) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3107_2394 : (Triangular src3107) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3107_2403 : (Triangular src3107) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3107_2431 : (Triangular src3107) 2431 2517 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3107_2518 : (Triangular src3107) 2518 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3107 : Cover (Triangular src3107) 2534 2390 [2390,2393,2402,2430,2517,2534] := by
  exact ⟨by decide, by decide, pass3107_2390, by decide, by decide, pass3107_2391, by decide, by decide, pass3107_2394, by decide, by decide, pass3107_2403, by decide, by decide, pass3107_2431, by decide, by decide, pass3107_2518, rfl⟩
def src3108 : Request := ⟨⟨⟨470,655,144,5315⟩,3184589537280,5168862572⟩,8,6,1,771221,26⟩
private theorem pass3108_2390 : (Triangular src3108) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3108_2391 : (Triangular src3108) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3108_2394 : (Triangular src3108) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3108_2403 : (Triangular src3108) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3108_2430 : (Triangular src3108) 2430 2509 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3108_2510 : (Triangular src3108) 2510 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3108 : Cover (Triangular src3108) 2534 2390 [2390,2393,2402,2429,2509,2534] := by
  exact ⟨by decide, by decide, pass3108_2390, by decide, by decide, pass3108_2391, by decide, by decide, pass3108_2394, by decide, by decide, pass3108_2403, by decide, by decide, pass3108_2430, by decide, by decide, pass3108_2510, rfl⟩
def src3109 : Request := ⟨⟨⟨690,962,212,7625⟩,10065769922560,23997864317⟩,16,6,1,771221,26⟩
private theorem pass3109_2390 : (Triangular src3109) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3109_2391 : (Triangular src3109) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3109_2393 : (Triangular src3109) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3109_2399 : (Triangular src3109) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3109_2416 : (Triangular src3109) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3109_2464 : (Triangular src3109) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3109 : Cover (Triangular src3109) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3109_2390, by decide, by decide, pass3109_2391, by decide, by decide, pass3109_2393, by decide, by decide, pass3109_2399, by decide, by decide, pass3109_2416, by decide, by decide, pass3109_2464, rfl⟩
def src3110 : Request := ⟨⟨⟨1000,1394,307,12883⟩,30557599170560,105471636407⟩,32,6,1,771221,26⟩
private theorem pass3110_2390 : (Triangular src3110) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3110_2391 : (Triangular src3110) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3110_2393 : (Triangular src3110) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3110_2399 : (Triangular src3110) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3110_2415 : (Triangular src3110) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3110_2459 : (Triangular src3110) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3110 : Cover (Triangular src3110) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3110_2390, by decide, by decide, pass3110_2391, by decide, by decide, pass3110_2393, by decide, by decide, pass3110_2399, by decide, by decide, pass3110_2415, by decide, by decide, pass3110_2459, rfl⟩
def src3111 : Request := ⟨⟨⟨1750,2440,537,17437⟩,163381988556800,986966790957⟩,50,6,1,771221,26⟩
private theorem pass3111_2390 : (Triangular src3111) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3111_2391 : (Triangular src3111) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3111_2393 : (Triangular src3111) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3111_2398 : (Triangular src3111) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3111_2412 : (Triangular src3111) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3111_2449 : (Triangular src3111) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3111 : Cover (Triangular src3111) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3111_2390, by decide, by decide, pass3111_2391, by decide, by decide, pass3111_2393, by decide, by decide, pass3111_2398, by decide, by decide, pass3111_2412, by decide, by decide, pass3111_2449, rfl⟩
def src3112 : Request := ⟨⟨⟨1450,2021,445,30737⟩,92998964346880,465028319332⟩,65,6,1,771221,26⟩
private theorem pass3112_2390 : (Triangular src3112) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3112_2391 : (Triangular src3112) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3112_2393 : (Triangular src3112) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3112_2399 : (Triangular src3112) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3112_2415 : (Triangular src3112) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3112_2457 : (Triangular src3112) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3112 : Cover (Triangular src3112) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3112_2390, by decide, by decide, pass3112_2391, by decide, by decide, pass3112_2393, by decide, by decide, pass3112_2399, by decide, by decide, pass3112_2415, by decide, by decide, pass3112_2457, rfl⟩
def src3113 : Request := ⟨⟨⟨2600,3625,819,27218⟩,546063062138880,4901614794409⟩,85,6,1,771221,26⟩
private theorem pass3113_2390 : (Triangular src3113) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3113_2391 : (Triangular src3113) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3113_2393 : (Triangular src3113) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3113_2398 : (Triangular src3113) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3113_2411 : (Triangular src3113) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3113_2445 : (Triangular src3113) 2445 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3113 : Cover (Triangular src3113) 2534 2390 [2390,2392,2397,2410,2444,2534] := by
  exact ⟨by decide, by decide, pass3113_2390, by decide, by decide, pass3113_2391, by decide, by decide, pass3113_2393, by decide, by decide, pass3113_2398, by decide, by decide, pass3113_2411, by decide, by decide, pass3113_2445, rfl⟩
def src3114 : Request := ⟨⟨⟨4800,6690,1512,109110⟩,3433136573644800,56816483122989⟩,245,6,1,771221,26⟩
private theorem pass3114_2390 : (Triangular src3114) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3114_2391 : (Triangular src3114) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3114_2393 : (Triangular src3114) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3114_2398 : (Triangular src3114) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3114_2411 : (Triangular src3114) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3114_2445 : (Triangular src3114) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3114_2532 : (Triangular src3114) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3114 : Cover (Triangular src3114) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3114_2390, by decide, by decide, pass3114_2391, by decide, by decide, pass3114_2393, by decide, by decide, pass3114_2398, by decide, by decide, pass3114_2411, by decide, by decide, pass3114_2445, by decide, by decide, pass3114_2532, rfl⟩
def src3115 : Request := ⟨⟨⟨6900,9621,2118,74442⟩,9997036108906496,238016971510476⟩,245,6,1,771221,26⟩
private theorem pass3115_2390 : (Triangular src3115) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3115_2391 : (Triangular src3115) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3115_2393 : (Triangular src3115) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3115_2398 : (Triangular src3115) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3115_2411 : (Triangular src3115) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3115_2445 : (Triangular src3115) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3115_2532 : (Triangular src3115) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3115 : Cover (Triangular src3115) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3115_2390, by decide, by decide, pass3115_2391, by decide, by decide, pass3115_2393, by decide, by decide, pass3115_2398, by decide, by decide, pass3115_2411, by decide, by decide, pass3115_2445, by decide, by decide, pass3115_2532, rfl⟩
def src3116 : Request := ⟨⟨⟨275,383,83,2196⟩,635228389376,603020643⟩,0,6,1,771221,41⟩
private theorem pass3116_2390 : (Triangular src3116) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3116_2391 : (Triangular src3116) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3116_2394 : (Triangular src3116) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3116_2404 : (Triangular src3116) 2404 2438 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3116_2439 : (Triangular src3116) 2439 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3116 : Cover (Triangular src3116) 2534 2390 [2390,2393,2403,2438,2534] := by
  exact ⟨by decide, by decide, pass3116_2390, by decide, by decide, pass3116_2391, by decide, by decide, pass3116_2394, by decide, by decide, pass3116_2404, by decide, by decide, pass3116_2439, rfl⟩
def src3117 : Request := ⟨⟨⟨325,453,98,2467⟩,1045036793856,1174588250⟩,1,6,1,771221,41⟩
private theorem pass3117_2390 : (Triangular src3117) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3117_2391 : (Triangular src3117) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3117_2394 : (Triangular src3117) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3117_2404 : (Triangular src3117) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3117_2436 : (Triangular src3117) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3117 : Cover (Triangular src3117) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3117_2390, by decide, by decide, pass3117_2391, by decide, by decide, pass3117_2394, by decide, by decide, pass3117_2404, by decide, by decide, pass3117_2436, rfl⟩
def src3118 : Request := ⟨⟨⟨325,453,98,2648⟩,1045036793856,1174588250⟩,2,6,1,771221,41⟩
private theorem pass3118_2390 : (Triangular src3118) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3118_2391 : (Triangular src3118) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3118_2394 : (Triangular src3118) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3118_2404 : (Triangular src3118) 2404 2436 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3118_2437 : (Triangular src3118) 2437 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3118 : Cover (Triangular src3118) 2534 2390 [2390,2393,2403,2436,2534] := by
  exact ⟨by decide, by decide, pass3118_2390, by decide, by decide, pass3118_2391, by decide, by decide, pass3118_2394, by decide, by decide, pass3118_2404, by decide, by decide, pass3118_2437, rfl⟩
def src3119 : Request := ⟨⟨⟨325,453,100,2779⟩,1061047500800,1193036697⟩,3,6,1,771221,41⟩
private theorem pass3119_2390 : (Triangular src3119) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3119_2391 : (Triangular src3119) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3119_2394 : (Triangular src3119) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3119_2404 : (Triangular src3119) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3119_2436 : (Triangular src3119) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3119 : Cover (Triangular src3119) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3119_2390, by decide, by decide, pass3119_2391, by decide, by decide, pass3119_2394, by decide, by decide, pass3119_2404, by decide, by decide, pass3119_2436, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2141

-- Source: Research6969.PrefixRescueDataMiddle16
section Z6969Source2142
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle16
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,25⟩
  bank i := ![bank101 3691, bank133 4635, bank142 5204, bank156 6628, bank201 11125, bank233 18387, bank261 36629, bank231 40774, bank363 92759, bank317 149537, bank349 94697] i
  reserve i := ![0, 2, 4, 8, 20, 40, 85, 65, 245, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 16

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 3691
    · exact rank133 4635
    · exact rank142 5204
    · exact rank156 6628
    · exact rank201 11125
    · exact rank233 18387
    · exact rank261 36629
    · exact rank231 40774
    · exact rank363 92759
    · exact rank317 149537
    · exact rank349 94697
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3094⟩
    · exact ⟨_, cover3095⟩
    · exact ⟨_, cover3096⟩
    · exact ⟨_, cover3097⟩
    · exact ⟨_, cover3098⟩
    · exact ⟨_, cover3099⟩
    · exact ⟨_, cover3101⟩
    · exact ⟨_, cover3100⟩
    · exact ⟨_, cover3104⟩
    · exact ⟨_, cover3102⟩
    · exact ⟨_, cover3103⟩

def price : EarlyPrice := ⟨6, 25, 10, 75/100, 70/100, ![1456923588689, 342204655434, 25477675655, 5095552390], 778097542004083⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7030/123, 147647/246, 269569/82, 2318975/246] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle16
end Z6969Source2142

-- Source: Research6969.PrefixMiddleSaved16
section Z6969Source2143
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved16
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle16.price Lower6960.Prefix6969RescueData.Middle16.price :=
  ⟨342, 3634, 57, 600, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle16.plan Lower6960.Prefix6969RescueData.Middle16.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 6 16 25 :=
  ⟨Lower6960.Prefix6969MainCases.Middle16.plan, Lower6960.Prefix6969MainCases.Middle16.price, Lower6960.Prefix6969MainCases.Middle16.valid, Lower6960.Prefix6969MainCases.Middle16.priced, Lower6960.Prefix6969MainCases.Middle16.sources,
   Lower6960.Prefix6969RescueData.Middle16.plan, Lower6960.Prefix6969RescueData.Middle16.price, Lower6960.Prefix6969RescueData.Middle16.sources, Lower6960.Prefix6969RescueData.Middle16.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved16
end Z6969Source2143

end Merged_Z6969Pack0757

-- merged module Z6969Pack0758
section Merged_Z6969Pack0758

-- Source: Research6969.PrefixMainDataMiddle23
section Z6969Source2144
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle23
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank108 3149, bank139 4010, bank167 13649, bank199 7608, bank171 27879] i
  head := src3214
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![16039, 124355, 572513, 1976185],
    ![24861/2, 89298, 1628487/4, 1454436],
    ![6218, 390227/9, 1628487/4, 1348413],
    ![29433/8, 420441/16, 634642/3, 659412],
    ![17323/9, 161789/12, 2184693/16, 6708249/16],
    ![81680/81, 193000/27, 217537/3, 915849/4],
    ![81680/81, 193000/27, 217537/3, 915849/4],
    ![76938/121, 524264/121, 4472669/98, 13310823/98],
    ![76938/121, 640967/150, 5052600/121, 5085081/40],
    ![55840/147, 640967/150, 5052600/121, 5085081/40],
    ![55840/147, 1580830/441, 32063787/968, 192954096/1849],
    ![1826342/5329, 1580830/441, 32063787/968, 192954096/1849]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 26 771221 := by
  refine ⟨?_, rank154 4227, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3214⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free108_2
    · exact free139_1
    · exact free167_1
    · exact free199_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [239985773, 305437027, 305531502, 305284595, 306197049, 147285048, 147271224, 111053365, 74153110, 90096752, 99178429, 223504706], [1532196, 1163772, 1163289, 1164553, 1159880, 2614855, 2615085, 3545300, 5401894, 4415243, 3993661, 1667847],
  ![118640768038920, 1619315999044, 201154235400, 5509931880], 128934723830292620⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1580830/441, 32063787/968, 192954096/1849] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle23
end Z6969Source2144

-- Source: Research6969.PrefixRescueDataMiddle23
section Z6969Source2145
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle23
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,40⟩
  bank i := ![bank78 2987, bank101 3195, bank133 4267, bank142 5315, bank193 7625, bank218 12883, bank240 17437, bank231 30737, bank263 27218, bank349 74442, bank318 109110] i
  reserve i := ![0, 1, 4, 8, 16, 32, 50, 65, 85, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 26

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank78 2987
    · exact rank101 3195
    · exact rank133 4267
    · exact rank142 5315
    · exact rank193 7625
    · exact rank218 12883
    · exact rank240 17437
    · exact rank231 30737
    · exact rank263 27218
    · exact rank349 74442
    · exact rank318 109110
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3105⟩
    · exact ⟨_, cover3106⟩
    · exact ⟨_, cover3107⟩
    · exact ⟨_, cover3108⟩
    · exact ⟨_, cover3109⟩
    · exact ⟨_, cover3110⟩
    · exact ⟨_, cover3111⟩
    · exact ⟨_, cover3112⟩
    · exact ⟨_, cover3113⟩
    · exact ⟨_, cover3115⟩
    · exact ⟨_, cover3114⟩

def price : EarlyPrice := ⟨6, 40, 10, 70/100, 60/100, ![1700875637520, 293328154956, 33016722576, 4127105148], 810850403524705⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2375/41, 647, 138582/41, 496280/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle23
end Z6969Source2145

-- Source: Research6969.PrefixMiddleSaved23
section Z6969Source2146
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved23
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle23.price Lower6960.Prefix6969RescueData.Middle23.price :=
  ⟨342, 3584, 57, 647, true⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle23.plan Lower6960.Prefix6969RescueData.Middle23.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    exact ⟨by decide, by decide +kernel⟩
  · rw [Budget.extra, Budget.adjust]
    decide +kernel

def data : Case 6 26 40 :=
  ⟨Lower6960.Prefix6969MainCases.Middle23.plan, Lower6960.Prefix6969MainCases.Middle23.price, Lower6960.Prefix6969MainCases.Middle23.valid, Lower6960.Prefix6969MainCases.Middle23.priced, Lower6960.Prefix6969MainCases.Middle23.sources,
   Lower6960.Prefix6969RescueData.Middle23.plan, Lower6960.Prefix6969RescueData.Middle23.price, Lower6960.Prefix6969RescueData.Middle23.sources, Lower6960.Prefix6969RescueData.Middle23.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved23
end Z6969Source2146

-- Source: Research6969.PrefixMainDataMiddle24
section Z6969Source2147
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle24
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 9, 13, 15, 21, 30, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1102, bank11 1192, bank19 1276, bank24 1404, bank33 1472, bank37 1587, bank45 1806, bank55 1948, bank72 2320, bank65 2772, bank123 3043, bank168 3916, bank136 8209, bank159 5020, bank199 7608, bank167 13649, bank230 11634, bank172 23613, bank171 27879] i
  head := src3215
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15979, 122179, 560384, 1876187],
    ![12581, 342093/4, 393360, 1420864],
    ![6218, 371449/9, 393360, 1202311],
    ![29433/8, 400747/16, 1815074/9, 587964],
    ![65616/25, 431152/25, 158976, 541696],
    ![17323/9, 154003/12, 2080727/16, 5981403/16],
    ![38747/32, 521853/64, 2351558/25, 6806814/25],
    ![45497/50, 583683/100, 72563, 1835503/9],
    ![45497/50, 583683/100, 342432/5, 1835503/9],
    ![13307/16, 583683/100, 6918268/121, 1835503/9],
    ![84176/121, 503053/121, 2184690/49, 11469067/98],
    ![84176/121, 503053/121, 2184690/49, 11069553/100],
    ![86337/200, 503053/121, 2184690/49, 11069553/100],
    ![86337/200, 60519/16, 27276116/729, 11069553/100],
    ![86337/200, 71570/21, 17331024/529, 4779092/49],
    ![55840/147, 71570/21, 17331024/529, 4779092/49],
    ![55840/147, 1015135/306, 1130437/36, 33837489/361],
    ![1872696/5329, 1015135/306, 1130437/36, 33837489/361],
    ![1826342/5329, 1015135/306, 1130437/36, 33837489/361]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 6 41 771221 := by
  refine ⟨?_, rank154 3769, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3215⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free11_1
    · exact free19_1
    · exact free24_1
    · exact free33_2
    · exact free37_1
    · exact free45_1
    · exact free55_1
    · exact free72_1
    · exact free65_1
    · exact free123_1
    · exact free168_1
    · exact free136_1
    · exact free159_1
    · exact free199_1
    · exact free167_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [229041889, 291013950, 289408217, 289263478, 289818284, 290342834, 290880095, 115201093, 115398663, 114337204, 96818562, 51941938, 55000000, 61588402, 72880497, 118347785, 95727120, 100000000, 221076728], [1622272, 1237638, 1245861, 1246603, 1243761, 1241075, 1238323, 3401346, 3395817, 3431180, 4093368, 7798511, 7352332, 6543248, 5503148, 3313288, 4139482, 3958949, 1687831],
  ![117351948756960, 1621950426172, 201191234500, 6674112960], 122375994164129789⟩

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
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 21 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1015135/306, 1130437/36, 33837489/361] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle24
end Z6969Source2147

-- Source: Research6969.PrefixRescueDataMiddle24
section Z6969Source2148
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle24
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,56⟩
  bank i := ![bank78 2196, bank100 2467, bank100 2648, bank101 2779, bank134 3437, bank156 4950, bank225 10568, bank231 19132, bank240 16270, bank319 42990, bank318 66149] i
  reserve i := ![0, 1, 2, 3, 6, 13, 40, 65, 65, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771221
  seedFloor := 41

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank78 2196
    · exact rank100 2467
    · exact rank100 2648
    · exact rank101 2779
    · exact rank134 3437
    · exact rank156 4950
    · exact rank225 10568
    · exact rank231 19132
    · exact rank240 16270
    · exact rank319 42990
    · exact rank318 66149
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3116⟩
    · exact ⟨_, cover3117⟩
    · exact ⟨_, cover3118⟩
    · exact ⟨_, cover3119⟩
    · exact ⟨_, cover3120⟩
    · exact ⟨_, cover3121⟩
    · exact ⟨_, cover3122⟩
    · exact ⟨_, cover3123⟩
    · exact ⟨_, cover3124⟩
    · exact ⟨_, cover3125⟩
    · exact ⟨_, cover3126⟩

def price : EarlyPrice := ⟨6, 56, 10, 65/100, 70/100, ![1443641266367, 241902117088, 32998013496, 2946262032], 766586101839450⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2375/41, 150821/246, 128589/41, 2407440/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle24
end Z6969Source2148

-- Source: Research6969.PrefixMiddleSaved24
section Z6969Source2149
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved24
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle24.price Lower6960.Prefix6969RescueData.Middle24.price :=
  ⟨342, 3317, 57, 613, true⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle24.plan Lower6960.Prefix6969RescueData.Middle24.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    exact ⟨by decide, by decide +kernel⟩
  · rw [Budget.extra, Budget.adjust]
    decide +kernel

def data : Case 6 41 56 :=
  ⟨Lower6960.Prefix6969MainCases.Middle24.plan, Lower6960.Prefix6969MainCases.Middle24.price, Lower6960.Prefix6969MainCases.Middle24.valid, Lower6960.Prefix6969MainCases.Middle24.priced, Lower6960.Prefix6969MainCases.Middle24.sources,
   Lower6960.Prefix6969RescueData.Middle24.plan, Lower6960.Prefix6969RescueData.Middle24.price, Lower6960.Prefix6969RescueData.Middle24.sources, Lower6960.Prefix6969RescueData.Middle24.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved24
end Z6969Source2149

-- Source: Research6969.PrefixMiddleSelect6
section Z6969Source2150
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer
set_option maxHeartbeats 8000000

theorem choose6 (j : Fin 56) :
    ∃ l u : ℕ, l≤j.val+1 ∧ j.val+1≤u ∧ Nonempty (Case 6 l u) := by
  fin_cases j
  · exact ⟨1, 1, by decide, by decide, ⟨Saved12.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved13.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved13.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved14.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved14.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved14.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved14.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved14.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved15.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved16.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved23.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved24.data⟩⟩

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source2150

-- Source: Research6969.PhysicalChecks201
section Z6969Source2151
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3216 : Request := ⟨⟨⟨556,772,170,5011⟩,5255817068544,9968090926⟩,10,8,2,1028294,2⟩
private theorem pass3216_2390 : (Triangular src3216) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3216_2391 : (Triangular src3216) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3216_2394 : (Triangular src3216) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3216_2402 : (Triangular src3216) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3216_2426 : (Triangular src3216) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3216_2496 : (Triangular src3216) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3216 : Cover (Triangular src3216) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3216_2390, by decide, by decide, pass3216_2391, by decide, by decide, pass3216_2394, by decide, by decide, pass3216_2402, by decide, by decide, pass3216_2426, by decide, by decide, pass3216_2496, rfl⟩
def src3217 : Request := ⟨⟨⟨556,772,170,4970⟩,5255817068544,9968090926⟩,10,8,2,1028294,3⟩
private theorem pass3217_2390 : (Triangular src3217) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3217_2391 : (Triangular src3217) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3217_2393 : (Triangular src3217) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3217_2399 : (Triangular src3217) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3217_2417 : (Triangular src3217) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3217_2469 : (Triangular src3217) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3217 : Cover (Triangular src3217) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3217_2390, by decide, by decide, pass3217_2391, by decide, by decide, pass3217_2393, by decide, by decide, pass3217_2399, by decide, by decide, pass3217_2417, by decide, by decide, pass3217_2469, rfl⟩
def src3218 : Request := ⟨⟨⟨556,772,170,4890⟩,5255817068544,9968090926⟩,10,8,2,1028294,5⟩
private theorem pass3218_2390 : (Triangular src3218) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3218_2391 : (Triangular src3218) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3218_2394 : (Triangular src3218) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3218_2402 : (Triangular src3218) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3218_2426 : (Triangular src3218) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3218_2496 : (Triangular src3218) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3218 : Cover (Triangular src3218) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass3218_2390, by decide, by decide, pass3218_2391, by decide, by decide, pass3218_2394, by decide, by decide, pass3218_2402, by decide, by decide, pass3218_2426, by decide, by decide, pass3218_2496, rfl⟩
def src3219 : Request := ⟨⟨⟨556,772,170,4695⟩,5255817068544,9968090926⟩,10,8,2,1028294,10⟩
private theorem pass3219_2390 : (Triangular src3219) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3219_2391 : (Triangular src3219) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3219_2393 : (Triangular src3219) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3219_2399 : (Triangular src3219) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3219_2417 : (Triangular src3219) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3219_2469 : (Triangular src3219) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3219 : Cover (Triangular src3219) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3219_2390, by decide, by decide, pass3219_2391, by decide, by decide, pass3219_2393, by decide, by decide, pass3219_2399, by decide, by decide, pass3219_2417, by decide, by decide, pass3219_2469, rfl⟩
def src3220 : Request := ⟨⟨⟨556,772,170,4438⟩,5255817068544,9968090926⟩,10,8,2,1028294,17⟩
private theorem pass3220_2390 : (Triangular src3220) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3220_2391 : (Triangular src3220) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3220_2393 : (Triangular src3220) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3220_2399 : (Triangular src3220) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3220_2417 : (Triangular src3220) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3220_2469 : (Triangular src3220) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3220 : Cover (Triangular src3220) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3220_2390, by decide, by decide, pass3220_2391, by decide, by decide, pass3220_2393, by decide, by decide, pass3220_2399, by decide, by decide, pass3220_2417, by decide, by decide, pass3220_2469, rfl⟩
def src3221 : Request := ⟨⟨⟨556,772,170,4108⟩,5255817068544,9968090926⟩,10,8,2,1028294,27⟩
private theorem pass3221_2390 : (Triangular src3221) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3221_2391 : (Triangular src3221) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3221_2393 : (Triangular src3221) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3221_2399 : (Triangular src3221) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3221_2417 : (Triangular src3221) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3221_2469 : (Triangular src3221) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3221 : Cover (Triangular src3221) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3221_2390, by decide, by decide, pass3221_2391, by decide, by decide, pass3221_2393, by decide, by decide, pass3221_2399, by decide, by decide, pass3221_2417, by decide, by decide, pass3221_2469, rfl⟩
def src3222 : Request := ⟨⟨⟨556,772,170,3710⟩,5255817068544,9968090926⟩,10,8,2,1028294,42⟩
private theorem pass3222_2390 : (Triangular src3222) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3222_2391 : (Triangular src3222) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3222_2393 : (Triangular src3222) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3222_2399 : (Triangular src3222) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3222_2417 : (Triangular src3222) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3222_2469 : (Triangular src3222) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3222 : Cover (Triangular src3222) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3222_2390, by decide, by decide, pass3222_2391, by decide, by decide, pass3222_2393, by decide, by decide, pass3222_2399, by decide, by decide, pass3222_2417, by decide, by decide, pass3222_2469, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2151

-- Source: Research6969.PrefixMainDataMiddle17
section Z6969Source2152
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle17
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank28 1523, bank37 1587, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank122 10626, bank159 5020, bank199 7608, bank158 18445, bank230 11634, bank172 23613, bank171 27879] i
  head := src3216
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 125542, 581107, 2124384],
    ![24861/2, 96354, 1757847/4, 3021633/2],
    ![6218, 422371/9, 1757847/4, 3021633/2],
    ![29433/8, 454153/16, 2056022/9, 781716],
    ![62542/25, 489416/25, 312215/2, 2319529/4],
    ![17323/9, 175117/12, 2362661/16, 7952457/16],
    ![36739/32, 295607/32, 909052/9, 9450746/25],
    ![86036/121, 691733/121, 3125777/49, 1583476/7],
    ![86036/121, 691733/121, 3125777/49, 1583476/7],
    ![254619/484, 2216614/441, 771225/16, 2831215/14],
    ![254619/484, 2216614/441, 771225/16, 2831215/14],
    ![254619/484, 577573/121, 771225/16, 9259849/64],
    ![41249/100, 577573/121, 771225/16, 9259849/64],
    ![41249/100, 69213/16, 1960310/49, 6300100/49],
    ![41249/100, 571370/147, 4332756/121, 14296383/121],
    ![480716/1323, 571370/147, 4332756/121, 14296383/121],
    ![480716/1323, 1157965/306, 9858715/288, 48581645/432],
    ![1872696/5329, 1157965/306, 9858715/288, 48581645/432],
    ![1826342/5329, 1157965/306, 9858715/288, 48581645/432]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 1 899758 := by
  refine ⟨?_, rank154 5011, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3216⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free28_1
    · exact free37_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free122_1
    · exact free159_1
    · exact free199_1
    · exact free158_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [249504419, 317806646, 317701600, 318163221, 318555395, 317436444, 318846090, 146729087, 147237758, 146834290, 146774223, 70117426, 70138108, 68833213, 80536997, 124550565, 100945136, 100000000, 225157143], [1453851, 1100423, 1100961, 1098597, 1096589, 1102319, 1095100, 2625255, 2615642, 2622946, 2624265, 5722988, 5721343, 5836612, 4955470, 3139706, 3919016, 3958949, 1654246],
  ![119517914647260, 1617522919332, 211735960500, 5953344240], 136168531718733849⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1157965/306, 9858715/288, 48581645/432] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle17
end Z6969Source2152

-- Source: Research6969.PhysicalChecks196
section Z6969Source2153
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3136 : Request := ⟨⟨⟨325,453,98,4784⟩,1045036793856,1174588250⟩,2,7,1,899758,1⟩
private theorem pass3136_2390 : (Triangular src3136) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3136_2391 : (Triangular src3136) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3136_2394 : (Triangular src3136) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3136_2404 : (Triangular src3136) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3136_2436 : (Triangular src3136) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3136 : Cover (Triangular src3136) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3136_2390, by decide, by decide, pass3136_2391, by decide, by decide, pass3136_2394, by decide, by decide, pass3136_2404, by decide, by decide, pass3136_2436, rfl⟩
def src3137 : Request := ⟨⟨⟨400,558,123,5475⟩,1971918995456,2734096379⟩,4,7,1,899758,1⟩
private theorem pass3137_2390 : (Triangular src3137) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3137_2391 : (Triangular src3137) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3137_2394 : (Triangular src3137) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3137_2403 : (Triangular src3137) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3137_2430 : (Triangular src3137) 2430 2513 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3137_2514 : (Triangular src3137) 2514 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3137 : Cover (Triangular src3137) 2534 2390 [2390,2393,2402,2429,2513,2534] := by
  exact ⟨by decide, by decide, pass3137_2390, by decide, by decide, pass3137_2391, by decide, by decide, pass3137_2394, by decide, by decide, pass3137_2403, by decide, by decide, pass3137_2430, by decide, by decide, pass3137_2514, rfl⟩
def src3138 : Request := ⟨⟨⟨560,781,172,7147⟩,5388141854720,10440670587⟩,8,7,1,899758,1⟩
private theorem pass3138_2390 : (Triangular src3138) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3138_2391 : (Triangular src3138) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3138_2393 : (Triangular src3138) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3138_2399 : (Triangular src3138) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3138_2417 : (Triangular src3138) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3138_2469 : (Triangular src3138) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3138 : Cover (Triangular src3138) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3138_2390, by decide, by decide, pass3138_2391, by decide, by decide, pass3138_2393, by decide, by decide, pass3138_2399, by decide, by decide, pass3138_2417, by decide, by decide, pass3138_2469, rfl⟩
def src3139 : Request := ⟨⟨⟨690,962,212,9040⟩,10065769922560,23997864317⟩,13,7,1,899758,1⟩
private theorem pass3139_2390 : (Triangular src3139) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3139_2391 : (Triangular src3139) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3139_2393 : (Triangular src3139) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3139_2399 : (Triangular src3139) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3139_2416 : (Triangular src3139) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3139_2464 : (Triangular src3139) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3139 : Cover (Triangular src3139) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3139_2390, by decide, by decide, pass3139_2391, by decide, by decide, pass3139_2393, by decide, by decide, pass3139_2399, by decide, by decide, pass3139_2416, by decide, by decide, pass3139_2464, rfl⟩
def src3140 : Request := ⟨⟨⟨1000,1395,315,12039⟩,31157463285760,107844841957⟩,20,7,1,899758,1⟩
private theorem pass3140_2390 : (Triangular src3140) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3140_2391 : (Triangular src3140) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3140_2393 : (Triangular src3140) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3140_2399 : (Triangular src3140) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3140_2415 : (Triangular src3140) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3140_2459 : (Triangular src3140) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3140 : Cover (Triangular src3140) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3140_2390, by decide, by decide, pass3140_2391, by decide, by decide, pass3140_2393, by decide, by decide, pass3140_2399, by decide, by decide, pass3140_2415, by decide, by decide, pass3140_2459, rfl⟩
def src3141 : Request := ⟨⟨⟨1200,1673,368,16391⟩,52718727069696,218387554859⟩,32,7,1,899758,1⟩
private theorem pass3141_2390 : (Triangular src3141) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3141_2391 : (Triangular src3141) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3141_2393 : (Triangular src3141) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3141_2399 : (Triangular src3141) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3141_2415 : (Triangular src3141) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3141_2458 : (Triangular src3141) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3141 : Cover (Triangular src3141) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3141_2390, by decide, by decide, pass3141_2391, by decide, by decide, pass3141_2393, by decide, by decide, pass3141_2399, by decide, by decide, pass3141_2415, by decide, by decide, pass3141_2458, rfl⟩
def src3142 : Request := ⟨⟨⟨1750,2440,537,23463⟩,163381988556800,986966790957⟩,50,7,1,899758,1⟩
private theorem pass3142_2390 : (Triangular src3142) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3142_2391 : (Triangular src3142) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3142_2393 : (Triangular src3142) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3142_2398 : (Triangular src3142) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3142_2412 : (Triangular src3142) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3142_2449 : (Triangular src3142) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3142 : Cover (Triangular src3142) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3142_2390, by decide, by decide, pass3142_2391, by decide, by decide, pass3142_2393, by decide, by decide, pass3142_2398, by decide, by decide, pass3142_2412, by decide, by decide, pass3142_2449, rfl⟩
def src3143 : Request := ⟨⟨⟨3200,4462,982,46573⟩,997767489781760,11020095796464⟩,110,7,1,899758,1⟩
private theorem pass3143_2390 : (Triangular src3143) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3143_2391 : (Triangular src3143) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3143_2393 : (Triangular src3143) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3143_2398 : (Triangular src3143) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3143_2411 : (Triangular src3143) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3143_2445 : (Triangular src3143) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3143_2534 : (Triangular src3143) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3143 : Cover (Triangular src3143) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3143_2390, by decide, by decide, pass3143_2391, by decide, by decide, pass3143_2393, by decide, by decide, pass3143_2398, by decide, by decide, pass3143_2411, by decide, by decide, pass3143_2445, by decide, by decide, pass3143_2534, rfl⟩
def src3144 : Request := ⟨⟨⟨8300,11575,2615,101037⟩,17745461310914560,508734991702659⟩,245,7,1,899758,1⟩
private theorem pass3144_2390 : (Triangular src3144) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3144_2391 : (Triangular src3144) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3144_2393 : (Triangular src3144) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3144_2398 : (Triangular src3144) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3144_2411 : (Triangular src3144) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3144_2444 : (Triangular src3144) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3144_2529 : (Triangular src3144) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3144 : Cover (Triangular src3144) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3144_2390, by decide, by decide, pass3144_2391, by decide, by decide, pass3144_2393, by decide, by decide, pass3144_2398, by decide, by decide, pass3144_2411, by decide, by decide, pass3144_2444, by decide, by decide, pass3144_2529, rfl⟩
def src3145 : Request := ⟨⟨⟨325,453,100,3952⟩,1061047500800,1193036697⟩,0,7,1,899758,2⟩
private theorem pass3145_2390 : (Triangular src3145) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3145_2391 : (Triangular src3145) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3145_2394 : (Triangular src3145) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3145_2404 : (Triangular src3145) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3145_2436 : (Triangular src3145) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3145 : Cover (Triangular src3145) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3145_2390, by decide, by decide, pass3145_2391, by decide, by decide, pass3145_2394, by decide, by decide, pass3145_2404, by decide, by decide, pass3145_2436, rfl⟩
def src3146 : Request := ⟨⟨⟨325,453,98,4351⟩,1045036793856,1174588250⟩,1,7,1,899758,2⟩
private theorem pass3146_2390 : (Triangular src3146) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3146_2391 : (Triangular src3146) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3146_2394 : (Triangular src3146) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3146_2404 : (Triangular src3146) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3146_2436 : (Triangular src3146) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3146 : Cover (Triangular src3146) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3146_2390, by decide, by decide, pass3146_2391, by decide, by decide, pass3146_2394, by decide, by decide, pass3146_2404, by decide, by decide, pass3146_2436, rfl⟩
def src3147 : Request := ⟨⟨⟨325,453,98,5136⟩,1045036793856,1174588250⟩,3,7,1,899758,2⟩
private theorem pass3147_2390 : (Triangular src3147) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3147_2391 : (Triangular src3147) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3147_2394 : (Triangular src3147) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3147_2404 : (Triangular src3147) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3147_2436 : (Triangular src3147) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3147 : Cover (Triangular src3147) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3147_2390, by decide, by decide, pass3147_2391, by decide, by decide, pass3147_2394, by decide, by decide, pass3147_2404, by decide, by decide, pass3147_2436, rfl⟩
def src3148 : Request := ⟨⟨⟨470,655,148,6836⟩,3250957582336,5279398867⟩,8,7,1,899758,2⟩
private theorem pass3148_2390 : (Triangular src3148) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3148_2391 : (Triangular src3148) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3148_2394 : (Triangular src3148) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3148_2402 : (Triangular src3148) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3148_2426 : (Triangular src3148) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3148_2498 : (Triangular src3148) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3148 : Cover (Triangular src3148) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass3148_2390, by decide, by decide, pass3148_2391, by decide, by decide, pass3148_2394, by decide, by decide, pass3148_2402, by decide, by decide, pass3148_2426, by decide, by decide, pass3148_2498, rfl⟩
def src3149 : Request := ⟨⟨⟨690,962,208,9144⟩,9921631092736,23645774460⟩,13,7,1,899758,2⟩
private theorem pass3149_2390 : (Triangular src3149) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3149_2391 : (Triangular src3149) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3149_2393 : (Triangular src3149) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3149_2399 : (Triangular src3149) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3149_2416 : (Triangular src3149) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3149_2465 : (Triangular src3149) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3149 : Cover (Triangular src3149) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass3149_2390, by decide, by decide, pass3149_2391, by decide, by decide, pass3149_2393, by decide, by decide, pass3149_2399, by decide, by decide, pass3149_2416, by decide, by decide, pass3149_2465, rfl⟩
def src3150 : Request := ⟨⟨⟨825,1150,260,11365⟩,17518948515840,49918096074⟩,20,7,1,899758,2⟩
private theorem pass3150_2390 : (Triangular src3150) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3150_2391 : (Triangular src3150) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3150_2393 : (Triangular src3150) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3150_2399 : (Triangular src3150) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3150_2416 : (Triangular src3150) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3150_2463 : (Triangular src3150) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3150 : Cover (Triangular src3150) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass3150_2390, by decide, by decide, pass3150_2391, by decide, by decide, pass3150_2393, by decide, by decide, pass3150_2399, by decide, by decide, pass3150_2416, by decide, by decide, pass3150_2463, rfl⟩
def src3151 : Request := ⟨⟨⟨1750,2440,537,23105⟩,163381988556800,986966790957⟩,50,7,1,899758,2⟩
private theorem pass3151_2390 : (Triangular src3151) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3151_2391 : (Triangular src3151) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3151_2393 : (Triangular src3151) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3151_2398 : (Triangular src3151) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3151_2412 : (Triangular src3151) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3151_2449 : (Triangular src3151) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3151 : Cover (Triangular src3151) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3151_2390, by decide, by decide, pass3151_2391, by decide, by decide, pass3151_2393, by decide, by decide, pass3151_2398, by decide, by decide, pass3151_2412, by decide, by decide, pass3151_2449, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2153

-- Source: Research6969.PrefixRescueDataMiddle17
section Z6969Source2154
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle17
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,1⟩
  bank i := ![bank101 4013, bank101 4313, bank100 4784, bank134 5475, bank156 7147, bank193 9040, bank223 12039, bank224 16391, bank240 23463, bank296 46573, bank363 101037] i
  reserve i := ![0, 1, 2, 4, 8, 13, 20, 32, 50, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 1

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 4013
    · exact rank101 4313
    · exact rank100 4784
    · exact rank134 5475
    · exact rank156 7147
    · exact rank193 9040
    · exact rank223 12039
    · exact rank224 16391
    · exact rank240 23463
    · exact rank296 46573
    · exact rank363 101037
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3134⟩
    · exact ⟨_, cover3135⟩
    · exact ⟨_, cover3136⟩
    · exact ⟨_, cover3137⟩
    · exact ⟨_, cover3138⟩
    · exact ⟨_, cover3139⟩
    · exact ⟨_, cover3140⟩
    · exact ⟨_, cover3141⟩
    · exact ⟨_, cover3142⟩
    · exact ⟨_, cover3143⟩
    · exact ⟨_, cover3144⟩

def price : EarlyPrice := ⟨7, 1, 10, 95/100, 80/100, ![39376139640, 239746809337, 1019117800, 6114657115], 261241814702699⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![10354/111, 51826/123, 359417/123, 33679/82] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle17
end Z6969Source2154

-- Source: Research6969.PrefixMiddleSaved17
section Z6969Source2155
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved17
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle17.price Lower6960.Prefix6969RescueData.Middle17.price :=
  ⟨342, 3784, 93, 421, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle17.plan Lower6960.Prefix6969RescueData.Middle17.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 7 1 1 :=
  ⟨Lower6960.Prefix6969MainCases.Middle17.plan, Lower6960.Prefix6969MainCases.Middle17.price, Lower6960.Prefix6969MainCases.Middle17.valid, Lower6960.Prefix6969MainCases.Middle17.priced, Lower6960.Prefix6969MainCases.Middle17.sources,
   Lower6960.Prefix6969RescueData.Middle17.plan, Lower6960.Prefix6969RescueData.Middle17.price, Lower6960.Prefix6969RescueData.Middle17.sources, Lower6960.Prefix6969RescueData.Middle17.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved17
end Z6969Source2155

end Merged_Z6969Pack0758

-- merged module Z6969Pack0759
section Merged_Z6969Pack0759

-- Source: Research6969.PrefixMainDataMiddle18
section Z6969Source2156
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle18
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank28 1523, bank37 1587, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank122 10626, bank159 5020, bank199 7608, bank158 18445, bank230 11634, bank172 23613, bank171 27879] i
  head := src3217
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 125419, 580410, 2118726],
    ![24861/2, 95985, 875541/2, 1498455],
    ![6218, 140230/3, 875541/2, 1498455],
    ![29433/8, 226195/8, 2048068/9, 775320],
    ![62542/25, 97506/5, 312215/2, 2319529/4],
    ![17323/9, 14535, 1176677/8, 3943695/8],
    ![36739/32, 73625/8, 909052/9, 1874684/5],
    ![86036/121, 62650/11, 444882/7, 224360],
    ![86036/121, 62650/11, 444882/7, 224360],
    ![254619/484, 315640/63, 771225/16, 200575],
    ![254619/484, 315640/63, 771225/16, 200575],
    ![254619/484, 4753, 771225/16, 9259849/64],
    ![41249/100, 4753, 771225/16, 9259849/64],
    ![41249/100, 34463/8, 1960310/49, 6300100/49],
    ![41249/100, 1707140/441, 17301309/484, 14179410/121],
    ![480716/1323, 1707140/441, 17301309/484, 14179410/121],
    ![480716/1323, 576625/153, 14728315/432, 24092075/216],
    ![1872696/5329, 576625/153, 14728315/432, 24092075/216],
    ![1826342/5329, 576625/153, 14728315/432, 24092075/216]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 2 899758 := by
  refine ⟨?_, rank154 4970, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3217⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free28_1
    · exact free37_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free122_1
    · exact free159_1
    · exact free199_1
    · exact free158_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [248697088, 317545660, 316822379, 316869119, 316271261, 317493267, 316333535, 154922504, 154901323, 154945124, 154574555, 69947002, 69984857, 68666950, 81497660, 124199456, 100665208, 100000000, 224982047], [1460495, 1101760, 1105464, 1105225, 1108287, 1102028, 1107968, 2487735, 2488087, 2487358, 2493526, 5736548, 5733536, 5851696, 4898364, 3149532, 3930843, 3958949, 1655687],
  ![119424970188540, 1617712815688, 211139075200, 5968729920], 135696882926445749⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 576625/153, 14728315/432, 24092075/216] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle18
end Z6969Source2156

-- Source: Research6969.PhysicalChecks197
section Z6969Source2157
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3152 : Request := ⟨⟨⟨1750,2439,537,45432⟩,163381988556800,985665319192⟩,85,7,1,899758,2⟩
private theorem pass3152_2390 : (Triangular src3152) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3152_2391 : (Triangular src3152) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3152_2393 : (Triangular src3152) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3152_2398 : (Triangular src3152) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3152_2412 : (Triangular src3152) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3152_2449 : (Triangular src3152) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3152 : Cover (Triangular src3152) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3152_2390, by decide, by decide, pass3152_2391, by decide, by decide, pass3152_2393, by decide, by decide, pass3152_2398, by decide, by decide, pass3152_2412, by decide, by decide, pass3152_2449, rfl⟩
def src3153 : Request := ⟨⟨⟨3950,5507,1244,58495⟩,1913299978158080,26084011577468⟩,145,7,1,899758,2⟩
private theorem pass3153_2390 : (Triangular src3153) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3153_2391 : (Triangular src3153) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3153_2393 : (Triangular src3153) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3153_2398 : (Triangular src3153) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3153_2411 : (Triangular src3153) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3153_2445 : (Triangular src3153) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3153_2533 : (Triangular src3153) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3153 : Cover (Triangular src3153) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3153_2390, by decide, by decide, pass3153_2391, by decide, by decide, pass3153_2393, by decide, by decide, pass3153_2398, by decide, by decide, pass3153_2411, by decide, by decide, pass3153_2445, by decide, by decide, pass3153_2533, rfl⟩
def src3154 : Request := ⟨⟨⟨6900,9621,2174,96095⟩,10196763128627200,242895948111878⟩,245,7,1,899758,2⟩
private theorem pass3154_2390 : (Triangular src3154) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3154_2391 : (Triangular src3154) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3154_2393 : (Triangular src3154) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3154_2398 : (Triangular src3154) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3154_2411 : (Triangular src3154) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3154_2444 : (Triangular src3154) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3154_2529 : (Triangular src3154) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3154 : Cover (Triangular src3154) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass3154_2390, by decide, by decide, pass3154_2391, by decide, by decide, pass3154_2393, by decide, by decide, pass3154_2398, by decide, by decide, pass3154_2411, by decide, by decide, pass3154_2444, by decide, by decide, pass3154_2529, rfl⟩
def src3155 : Request := ⟨⟨⟨275,383,84,3725⟩,640970915840,608607683⟩,0,7,1,899758,4⟩
private theorem pass3155_2390 : (Triangular src3155) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3155_2391 : (Triangular src3155) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3155_2394 : (Triangular src3155) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3155_2404 : (Triangular src3155) 2404 2437 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3155_2438 : (Triangular src3155) 2438 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3155 : Cover (Triangular src3155) 2534 2390 [2390,2393,2403,2437,2534] := by
  exact ⟨by decide, by decide, pass3155_2390, by decide, by decide, pass3155_2391, by decide, by decide, pass3155_2394, by decide, by decide, pass3155_2404, by decide, by decide, pass3155_2438, rfl⟩
def src3156 : Request := ⟨⟨⟨325,453,98,4219⟩,1045036793856,1174588250⟩,1,7,1,899758,4⟩
private theorem pass3156_2390 : (Triangular src3156) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3156_2391 : (Triangular src3156) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3156_2394 : (Triangular src3156) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3156_2404 : (Triangular src3156) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3156_2436 : (Triangular src3156) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3156 : Cover (Triangular src3156) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3156_2390, by decide, by decide, pass3156_2391, by decide, by decide, pass3156_2394, by decide, by decide, pass3156_2404, by decide, by decide, pass3156_2436, rfl⟩
def src3157 : Request := ⟨⟨⟨325,453,98,4568⟩,1045036793856,1174588250⟩,2,7,1,899758,4⟩
private theorem pass3157_2390 : (Triangular src3157) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3157_2391 : (Triangular src3157) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3157_2394 : (Triangular src3157) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3157_2404 : (Triangular src3157) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3157_2436 : (Triangular src3157) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3157 : Cover (Triangular src3157) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3157_2390, by decide, by decide, pass3157_2391, by decide, by decide, pass3157_2394, by decide, by decide, pass3157_2404, by decide, by decide, pass3157_2436, rfl⟩
def src3158 : Request := ⟨⟨⟨325,453,98,5473⟩,1045036793856,1174588250⟩,4,7,1,899758,4⟩
private theorem pass3158_2390 : (Triangular src3158) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3158_2391 : (Triangular src3158) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3158_2394 : (Triangular src3158) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3158_2404 : (Triangular src3158) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3158_2436 : (Triangular src3158) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3158 : Cover (Triangular src3158) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3158_2390, by decide, by decide, pass3158_2391, by decide, by decide, pass3158_2394, by decide, by decide, pass3158_2404, by decide, by decide, pass3158_2436, rfl⟩
def src3159 : Request := ⟨⟨⟨470,655,144,6690⟩,3184589537280,5168862572⟩,8,7,1,899758,4⟩
private theorem pass3159_2390 : (Triangular src3159) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3159_2391 : (Triangular src3159) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3159_2393 : (Triangular src3159) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3159_2399 : (Triangular src3159) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3159_2417 : (Triangular src3159) 2417 2470 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3159_2471 : (Triangular src3159) 2471 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3159 : Cover (Triangular src3159) 2534 2390 [2390,2392,2398,2416,2470,2534] := by
  exact ⟨by decide, by decide, pass3159_2390, by decide, by decide, pass3159_2391, by decide, by decide, pass3159_2393, by decide, by decide, pass3159_2399, by decide, by decide, pass3159_2417, by decide, by decide, pass3159_2471, rfl⟩
def src3160 : Request := ⟨⟨⟨825,1150,253,11139⟩,17161575202816,48873782027⟩,20,7,1,899758,4⟩
private theorem pass3160_2390 : (Triangular src3160) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3160_2391 : (Triangular src3160) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3160_2393 : (Triangular src3160) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3160_2399 : (Triangular src3160) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3160_2416 : (Triangular src3160) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3160_2463 : (Triangular src3160) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3160 : Cover (Triangular src3160) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass3160_2390, by decide, by decide, pass3160_2391, by decide, by decide, pass3160_2393, by decide, by decide, pass3160_2399, by decide, by decide, pass3160_2416, by decide, by decide, pass3160_2463, rfl⟩
def src3161 : Request := ⟨⟨⟨825,1150,253,17888⟩,17161575202816,48873782027⟩,32,7,1,899758,4⟩
private theorem pass3161_2390 : (Triangular src3161) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3161_2391 : (Triangular src3161) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3161_2393 : (Triangular src3161) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3161_2399 : (Triangular src3161) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3161_2416 : (Triangular src3161) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3161_2463 : (Triangular src3161) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3161 : Cover (Triangular src3161) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass3161_2390, by decide, by decide, pass3161_2391, by decide, by decide, pass3161_2393, by decide, by decide, pass3161_2399, by decide, by decide, pass3161_2416, by decide, by decide, pass3161_2463, rfl⟩
def src3162 : Request := ⟨⟨⟨1450,2022,445,18660⟩,92998964346880,465769321795⟩,40,7,1,899758,4⟩
private theorem pass3162_2390 : (Triangular src3162) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3162_2391 : (Triangular src3162) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3162_2393 : (Triangular src3162) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3162_2399 : (Triangular src3162) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3162_2415 : (Triangular src3162) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3162_2457 : (Triangular src3162) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3162 : Cover (Triangular src3162) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass3162_2390, by decide, by decide, pass3162_2391, by decide, by decide, pass3162_2393, by decide, by decide, pass3162_2399, by decide, by decide, pass3162_2415, by decide, by decide, pass3162_2457, rfl⟩
def src3163 : Request := ⟨⟨⟨2600,3623,798,88020⟩,535425056505856,4795161706555⟩,145,7,1,899758,4⟩
private theorem pass3163_2390 : (Triangular src3163) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3163_2391 : (Triangular src3163) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3163_2393 : (Triangular src3163) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3163_2398 : (Triangular src3163) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3163_2411 : (Triangular src3163) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3163_2445 : (Triangular src3163) 2445 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3163 : Cover (Triangular src3163) 2534 2390 [2390,2392,2397,2410,2444,2534] := by
  exact ⟨by decide, by decide, pass3163_2390, by decide, by decide, pass3163_2391, by decide, by decide, pass3163_2393, by decide, by decide, pass3163_2398, by decide, by decide, pass3163_2411, by decide, by decide, pass3163_2445, rfl⟩
def src3164 : Request := ⟨⟨⟨3950,5507,1213,57467⟩,1877062482395136,25577387039299⟩,145,7,1,899758,4⟩
private theorem pass3164_2390 : (Triangular src3164) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3164_2391 : (Triangular src3164) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3164_2393 : (Triangular src3164) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3164_2398 : (Triangular src3164) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3164_2411 : (Triangular src3164) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3164_2445 : (Triangular src3164) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3164_2533 : (Triangular src3164) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3164 : Cover (Triangular src3164) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3164_2390, by decide, by decide, pass3164_2391, by decide, by decide, pass3164_2393, by decide, by decide, pass3164_2398, by decide, by decide, pass3164_2411, by decide, by decide, pass3164_2445, by decide, by decide, pass3164_2533, rfl⟩
def src3165 : Request := ⟨⟨⟨6900,9621,2118,94423⟩,9997036108906496,238016971510476⟩,245,7,1,899758,4⟩
private theorem pass3165_2390 : (Triangular src3165) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3165_2391 : (Triangular src3165) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3165_2393 : (Triangular src3165) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3165_2398 : (Triangular src3165) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3165_2411 : (Triangular src3165) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3165_2445 : (Triangular src3165) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3165_2532 : (Triangular src3165) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3165 : Cover (Triangular src3165) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3165_2390, by decide, by decide, pass3165_2391, by decide, by decide, pass3165_2393, by decide, by decide, pass3165_2398, by decide, by decide, pass3165_2411, by decide, by decide, pass3165_2445, by decide, by decide, pass3165_2532, rfl⟩
def src3166 : Request := ⟨⟨⟨325,453,100,3537⟩,1061047500800,1193036697⟩,0,7,1,899758,9⟩
private theorem pass3166_2390 : (Triangular src3166) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3166_2391 : (Triangular src3166) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3166_2394 : (Triangular src3166) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3166_2404 : (Triangular src3166) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3166_2436 : (Triangular src3166) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3166 : Cover (Triangular src3166) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3166_2390, by decide, by decide, pass3166_2391, by decide, by decide, pass3166_2394, by decide, by decide, pass3166_2404, by decide, by decide, pass3166_2436, rfl⟩
def src3167 : Request := ⟨⟨⟨325,453,98,3896⟩,1045036793856,1174588250⟩,1,7,1,899758,9⟩
private theorem pass3167_2390 : (Triangular src3167) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3167_2391 : (Triangular src3167) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3167_2394 : (Triangular src3167) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3167_2404 : (Triangular src3167) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3167_2436 : (Triangular src3167) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3167 : Cover (Triangular src3167) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3167_2390, by decide, by decide, pass3167_2391, by decide, by decide, pass3167_2394, by decide, by decide, pass3167_2404, by decide, by decide, pass3167_2436, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2157

-- Source: Research6969.PrefixRescueDataMiddle18
section Z6969Source2158
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle18
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,7,1,3⟩
  bank i := ![bank101 3952, bank100 4351, bank100 5136, bank143 6836, bank192 9144, bank202 11365, bank240 23105, bank239 45432, bank307 58495, bank350 96095] i
  reserve i := ![0, 1, 3, 8, 13, 20, 50, 85, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 2

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 3952
    · exact rank100 4351
    · exact rank100 5136
    · exact rank143 6836
    · exact rank192 9144
    · exact rank202 11365
    · exact rank240 23105
    · exact rank239 45432
    · exact rank307 58495
    · exact rank350 96095
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3145⟩
    · exact ⟨_, cover3146⟩
    · exact ⟨_, cover3147⟩
    · exact ⟨_, cover3148⟩
    · exact ⟨_, cover3149⟩
    · exact ⟨_, cover3150⟩
    · exact ⟨_, cover3151⟩
    · exact ⟨_, cover3152⟩
    · exact ⟨_, cover3153⟩
    · exact ⟨_, cover3154⟩

def price : EarlyPrice := ⟨7, 3, 9, 95/100, 80/100, ![112349661440, 233405709539, 2541736448, 5083466374], 288308601435038⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5661/86, 102617/246, 350764/123, 96095/82] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle18
end Z6969Source2158

-- Source: Research6969.PrefixMiddleSaved18
section Z6969Source2159
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved18
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle18.price Lower6960.Prefix6969RescueData.Middle18.price :=
  ⟨342, 3768, 65, 417, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle18.plan Lower6960.Prefix6969RescueData.Middle18.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 7 2 3 :=
  ⟨Lower6960.Prefix6969MainCases.Middle18.plan, Lower6960.Prefix6969MainCases.Middle18.price, Lower6960.Prefix6969MainCases.Middle18.valid, Lower6960.Prefix6969MainCases.Middle18.priced, Lower6960.Prefix6969MainCases.Middle18.sources,
   Lower6960.Prefix6969RescueData.Middle18.plan, Lower6960.Prefix6969RescueData.Middle18.price, Lower6960.Prefix6969RescueData.Middle18.sources, Lower6960.Prefix6969RescueData.Middle18.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved18
end Z6969Source2159

-- Source: Research6969.PrefixMainDataMiddle19
section Z6969Source2160
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle19
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank28 1523, bank37 1587, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank122 10626, bank159 5020, bank199 7608, bank158 18445, bank230 11634, bank171 27879] i
  head := src3218
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 125179, 579050, 2107686],
    ![24861/2, 95265, 868941/2, 1474335],
    ![6218, 417410/9, 868941/2, 1474335],
    ![29433/8, 224475/8, 677516/3, 762840],
    ![62542/25, 19354, 312215/2, 2319529/4],
    ![17323/9, 43265/3, 1167597/8, 3880215/8],
    ![36739/32, 73085/8, 909052/9, 1844508/5],
    ![86036/121, 684110/121, 3091534/49, 1545240/7],
    ![86036/121, 684110/121, 3091534/49, 1545240/7],
    ![254619/484, 2195560/441, 771225/16, 1381425/7],
    ![254619/484, 2195560/441, 771225/16, 1381425/7],
    ![254619/484, 570313/121, 771225/16, 9259849/64],
    ![41249/100, 570313/121, 771225/16, 9259849/64],
    ![41249/100, 34183/8, 1960310/49, 6300100/49],
    ![41249/100, 1693540/441, 17164629/484, 13951170/121],
    ![480716/1323, 1693540/441, 17164629/484, 13951170/121],
    ![480716/1323, 190675/51, 14611715/432, 2762244/25],
    ![1826342/5329, 190675/51, 14611715/432, 2762244/25]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 4 899758 := by
  refine ⟨?_, rank154 4890, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3218⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free28_1
    · exact free37_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free122_1
    · exact free159_1
    · exact free199_1
    · exact free158_1
    · exact free230_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [247121808, 315520695, 315559081, 315472880, 315329532, 314654369, 314515481, 147162387, 147055704, 147087099, 147071052, 69753772, 69847566, 68342535, 78924057, 123027857, 124089738, 224640395], [1473461, 1112130, 1111934, 1112375, 1113109, 1116567, 1117278, 2616897, 2618673, 2618150, 2618417, 5753098, 5744589, 5881127, 5065696, 3182318, 3152602, 1658500],
  ![119243614473900, 1618084027180, 209147356900, 5998749540], 134519086874442187⟩

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
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 190675/51, 14611715/432, 2762244/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle19
end Z6969Source2160

-- Source: Research6969.PrefixRescueDataMiddle19
section Z6969Source2161
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle19
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,8⟩
  bank i := ![bank79 3725, bank100 4219, bank100 4568, bank100 5473, bank142 6690, bank201 11139, bank201 17888, bank233 18660, bank306 57467, bank258 88020, bank349 94423] i
  reserve i := ![0, 1, 2, 4, 8, 20, 32, 40, 145, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 4

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank79 3725
    · exact rank100 4219
    · exact rank100 4568
    · exact rank100 5473
    · exact rank142 6690
    · exact rank201 11139
    · exact rank201 17888
    · exact rank233 18660
    · exact rank306 57467
    · exact rank258 88020
    · exact rank349 94423
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3155⟩
    · exact ⟨_, cover3156⟩
    · exact ⟨_, cover3157⟩
    · exact ⟨_, cover3158⟩
    · exact ⟨_, cover3159⟩
    · exact ⟨_, cover3160⟩
    · exact ⟨_, cover3161⟩
    · exact ⟨_, cover3162⟩
    · exact ⟨_, cover3164⟩
    · exact ⟨_, cover3163⟩
    · exact ⟨_, cover3165⟩

def price : EarlyPrice := ⟨7, 8, 10, 90/100, 80/100, ![294385419790, 244181723513, 6603352140, 4952521518], 359799049679726⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8411/146, 111367/246, 737929/246, 9212/3] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle19
end Z6969Source2161

-- Source: Research6969.PrefixMiddleSaved19
section Z6969Source2162
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved19
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle19.price Lower6960.Prefix6969RescueData.Middle19.price :=
  ⟨342, 3738, 57, 452, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle19.plan Lower6960.Prefix6969RescueData.Middle19.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 7 4 8 :=
  ⟨Lower6960.Prefix6969MainCases.Middle19.plan, Lower6960.Prefix6969MainCases.Middle19.price, Lower6960.Prefix6969MainCases.Middle19.valid, Lower6960.Prefix6969MainCases.Middle19.priced, Lower6960.Prefix6969MainCases.Middle19.sources,
   Lower6960.Prefix6969RescueData.Middle19.plan, Lower6960.Prefix6969RescueData.Middle19.price, Lower6960.Prefix6969RescueData.Middle19.sources, Lower6960.Prefix6969RescueData.Middle19.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved19
end Z6969Source2162

-- Source: Research6969.PrefixMainDataMiddle20
section Z6969Source2163
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle20
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 75, 105, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank33 1472, bank37 1587, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank124 10359, bank159 5020, bank199 7608, bank187 16602, bank230 11634, bank172 23613, bank171 27879] i
  head := src3219
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15024, 124607, 576015, 2077229],
    ![24861/2, 93510, 1705707/4, 1454436],
    ![6218, 409415/9, 1705707/4, 1454436],
    ![29433/8, 440565/16, 664906/3, 732420],
    ![65616/25, 19024, 158976, 541696],
    ![17323/9, 169745/12, 2290929/16, 7450965/16],
    ![36739/32, 287075/32, 909052/9, 1770954/5],
    ![86036/121, 61075/11, 3036349/49, 1483620/7],
    ![86036/121, 61075/11, 3036349/49, 1483620/7],
    ![254619/484, 2161630/441, 771225/16, 15642025/81],
    ![254619/484, 2161630/441, 771225/16, 15642025/81],
    ![254619/484, 50783/11, 771225/16, 9259849/64],
    ![20667/50, 50783/11, 771225/16, 9259849/64],
    ![20667/50, 67001/16, 1960310/49, 6300100/49],
    ![20667/50, 1660390/441, 33662943/968, 13394835/121],
    ![1960504/5329, 1660390/441, 33662943/968, 13394835/121],
    ![1960504/5329, 124625/34, 5813676/175, 546216300/5041],
    ![1872696/5329, 124625/34, 5813676/175, 546216300/5041],
    ![1826342/5329, 124625/34, 5813676/175, 546216300/5041]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 9 899758 := by
  refine ⟨?_, rank154 4695, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3219⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free33_2
    · exact free37_1
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free124_1
    · exact free159_1
    · exact free199_1
    · exact free187_1
    · exact free230_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [243473644, 310450673, 311054673, 311326176, 311029889, 311279506, 310729566, 145484831, 145516678, 145802952, 145648733, 69979938, 69998712, 67575717, 87879174, 122892878, 99175070, 100000000, 223857562], [1503488, 1138096, 1135002, 1133612, 1135129, 1133851, 1136667, 2652565, 2651866, 2645583, 2648968, 5733927, 5732434, 5950693, 4527191, 3186096, 3993803, 3958949, 1664943],
  ![118828071060840, 1618933276868, 208917892600, 6069706860], 133007866539334107⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 124625/34, 5813676/175, 546216300/5041] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle20
end Z6969Source2163

-- Source: Research6969.PhysicalChecks198
section Z6969Source2164
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3168 : Request := ⟨⟨⟨325,453,98,4596⟩,1045036793856,1174588250⟩,3,7,1,899758,9⟩
private theorem pass3168_2390 : (Triangular src3168) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3168_2391 : (Triangular src3168) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3168_2394 : (Triangular src3168) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3168_2404 : (Triangular src3168) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3168_2436 : (Triangular src3168) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3168 : Cover (Triangular src3168) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3168_2390, by decide, by decide, pass3168_2391, by decide, by decide, pass3168_2394, by decide, by decide, pass3168_2404, by decide, by decide, pass3168_2436, rfl⟩
def src3169 : Request := ⟨⟨⟨470,655,148,6108⟩,3250957582336,5279398867⟩,8,7,1,899758,9⟩
private theorem pass3169_2390 : (Triangular src3169) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3169_2391 : (Triangular src3169) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3169_2394 : (Triangular src3169) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3169_2402 : (Triangular src3169) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3169_2426 : (Triangular src3169) 2426 2497 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3169_2498 : (Triangular src3169) 2498 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3169 : Cover (Triangular src3169) 2534 2390 [2390,2393,2401,2425,2497,2534] := by
  exact ⟨by decide, by decide, pass3169_2390, by decide, by decide, pass3169_2391, by decide, by decide, pass3169_2394, by decide, by decide, pass3169_2402, by decide, by decide, pass3169_2426, by decide, by decide, pass3169_2498, rfl⟩
def src3170 : Request := ⟨⟨⟨825,1150,260,10158⟩,17518948515840,49918096074⟩,20,7,1,899758,9⟩
private theorem pass3170_2390 : (Triangular src3170) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3170_2391 : (Triangular src3170) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3170_2393 : (Triangular src3170) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3170_2399 : (Triangular src3170) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3170_2416 : (Triangular src3170) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3170_2463 : (Triangular src3170) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3170 : Cover (Triangular src3170) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass3170_2390, by decide, by decide, pass3170_2391, by decide, by decide, pass3170_2393, by decide, by decide, pass3170_2399, by decide, by decide, pass3170_2416, by decide, by decide, pass3170_2463, rfl⟩
def src3171 : Request := ⟨⟨⟨1000,1393,307,31947⟩,30557599170560,105228376929⟩,50,7,1,899758,9⟩
private theorem pass3171_2390 : (Triangular src3171) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3171_2391 : (Triangular src3171) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3171_2393 : (Triangular src3171) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3171_2399 : (Triangular src3171) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3171_2415 : (Triangular src3171) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3171_2459 : (Triangular src3171) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3171 : Cover (Triangular src3171) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3171_2390, by decide, by decide, pass3171_2391, by decide, by decide, pass3171_2393, by decide, by decide, pass3171_2399, by decide, by decide, pass3171_2415, by decide, by decide, pass3171_2459, rfl⟩
def src3172 : Request := ⟨⟨⟨2100,2928,645,25686⟩,282396798484480,2046887686018⟩,65,7,1,899758,9⟩
private theorem pass3172_2390 : (Triangular src3172) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3172_2391 : (Triangular src3172) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3172_2393 : (Triangular src3172) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3172_2398 : (Triangular src3172) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3172_2412 : (Triangular src3172) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3172_2449 : (Triangular src3172) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3172 : Cover (Triangular src3172) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3172_2390, by decide, by decide, pass3172_2391, by decide, by decide, pass3172_2393, by decide, by decide, pass3172_2398, by decide, by decide, pass3172_2412, by decide, by decide, pass3172_2449, rfl⟩
def src3173 : Request := ⟨⟨⟨3200,4459,1008,118544⟩,1017717693874176,11221829825062⟩,190,7,1,899758,9⟩
private theorem pass3173_2390 : (Triangular src3173) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3173_2391 : (Triangular src3173) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3173_2393 : (Triangular src3173) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3173_2398 : (Triangular src3173) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3173_2411 : (Triangular src3173) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3173_2445 : (Triangular src3173) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3173_2533 : (Triangular src3173) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3173 : Cover (Triangular src3173) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3173_2390, by decide, by decide, pass3173_2391, by decide, by decide, pass3173_2393, by decide, by decide, pass3173_2398, by decide, by decide, pass3173_2411, by decide, by decide, pass3173_2445, by decide, by decide, pass3173_2533, rfl⟩
def src3174 : Request := ⟨⟨⟨5700,7948,1750,68638⟩,5637370734182400,110890906752819⟩,190,7,1,899758,9⟩
private theorem pass3174_2390 : (Triangular src3174) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3174_2391 : (Triangular src3174) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3174_2393 : (Triangular src3174) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3174_2398 : (Triangular src3174) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3174_2411 : (Triangular src3174) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3174_2445 : (Triangular src3174) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3174_2533 : (Triangular src3174) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3174 : Cover (Triangular src3174) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3174_2390, by decide, by decide, pass3174_2391, by decide, by decide, pass3174_2393, by decide, by decide, pass3174_2398, by decide, by decide, pass3174_2411, by decide, by decide, pass3174_2445, by decide, by decide, pass3174_2533, rfl⟩
def src3175 : Request := ⟨⟨⟨3950,5504,1244,174005⟩,1913299978158080,26038250013848⟩,245,7,1,899758,9⟩
private theorem pass3175_2390 : (Triangular src3175) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3175_2391 : (Triangular src3175) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3175_2393 : (Triangular src3175) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3175_2398 : (Triangular src3175) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3175_2411 : (Triangular src3175) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3175_2445 : (Triangular src3175) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3175_2533 : (Triangular src3175) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3175 : Cover (Triangular src3175) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3175_2390, by decide, by decide, pass3175_2391, by decide, by decide, pass3175_2393, by decide, by decide, pass3175_2398, by decide, by decide, pass3175_2411, by decide, by decide, pass3175_2445, by decide, by decide, pass3175_2533, rfl⟩
def src3176 : Request := ⟨⟨⟨325,453,100,3154⟩,1061047500800,1193036697⟩,0,7,1,899758,16⟩
private theorem pass3176_2390 : (Triangular src3176) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3176_2391 : (Triangular src3176) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3176_2394 : (Triangular src3176) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3176_2403 : (Triangular src3176) 2403 2432 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3176_2433 : (Triangular src3176) 2433 2529 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3176_2530 : (Triangular src3176) 2530 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3176 : Cover (Triangular src3176) 2534 2390 [2390,2393,2402,2432,2529,2534] := by
  exact ⟨by decide, by decide, pass3176_2390, by decide, by decide, pass3176_2391, by decide, by decide, pass3176_2394, by decide, by decide, pass3176_2403, by decide, by decide, pass3176_2433, by decide, by decide, pass3176_2530, rfl⟩
def src3177 : Request := ⟨⟨⟨325,453,98,3473⟩,1045036793856,1174588250⟩,1,7,1,899758,16⟩
private theorem pass3177_2390 : (Triangular src3177) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3177_2391 : (Triangular src3177) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3177_2394 : (Triangular src3177) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3177_2404 : (Triangular src3177) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3177_2436 : (Triangular src3177) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3177 : Cover (Triangular src3177) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3177_2390, by decide, by decide, pass3177_2391, by decide, by decide, pass3177_2394, by decide, by decide, pass3177_2404, by decide, by decide, pass3177_2436, rfl⟩
def src3178 : Request := ⟨⟨⟨325,453,98,3755⟩,1045036793856,1174588250⟩,2,7,1,899758,16⟩
private theorem pass3178_2390 : (Triangular src3178) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3178_2391 : (Triangular src3178) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3178_2394 : (Triangular src3178) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3178_2404 : (Triangular src3178) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3178_2436 : (Triangular src3178) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3178 : Cover (Triangular src3178) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3178_2390, by decide, by decide, pass3178_2391, by decide, by decide, pass3178_2394, by decide, by decide, pass3178_2404, by decide, by decide, pass3178_2436, rfl⟩
def src3179 : Request := ⟨⟨⟨400,558,123,4298⟩,1971918995456,2734096379⟩,4,7,1,899758,16⟩
private theorem pass3179_2390 : (Triangular src3179) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3179_2391 : (Triangular src3179) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3179_2394 : (Triangular src3179) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3179_2403 : (Triangular src3179) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3179_2431 : (Triangular src3179) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3179_2517 : (Triangular src3179) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3179 : Cover (Triangular src3179) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass3179_2390, by decide, by decide, pass3179_2391, by decide, by decide, pass3179_2394, by decide, by decide, pass3179_2403, by decide, by decide, pass3179_2431, by decide, by decide, pass3179_2517, rfl⟩
def src3180 : Request := ⟨⟨⟨470,655,148,5427⟩,3250957582336,5279398867⟩,8,7,1,899758,16⟩
private theorem pass3180_2390 : (Triangular src3180) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3180_2391 : (Triangular src3180) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3180_2394 : (Triangular src3180) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3180_2403 : (Triangular src3180) 2403 2428 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3180_2429 : (Triangular src3180) 2429 2506 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3180_2507 : (Triangular src3180) 2507 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3180 : Cover (Triangular src3180) 2534 2390 [2390,2393,2402,2428,2506,2534] := by
  exact ⟨by decide, by decide, pass3180_2390, by decide, by decide, pass3180_2391, by decide, by decide, pass3180_2394, by decide, by decide, pass3180_2403, by decide, by decide, pass3180_2429, by decide, by decide, pass3180_2507, rfl⟩
def src3181 : Request := ⟨⟨⟨690,962,212,7913⟩,10065769922560,23997864317⟩,16,7,1,899758,16⟩
private theorem pass3181_2390 : (Triangular src3181) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3181_2391 : (Triangular src3181) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3181_2393 : (Triangular src3181) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3181_2399 : (Triangular src3181) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3181_2416 : (Triangular src3181) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3181_2464 : (Triangular src3181) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3181 : Cover (Triangular src3181) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass3181_2390, by decide, by decide, pass3181_2391, by decide, by decide, pass3181_2393, by decide, by decide, pass3181_2399, by decide, by decide, pass3181_2416, by decide, by decide, pass3181_2464, rfl⟩
def src3182 : Request := ⟨⟨⟨1200,1673,368,15403⟩,52718727069696,218387554859⟩,40,7,1,899758,16⟩
private theorem pass3182_2390 : (Triangular src3182) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3182_2391 : (Triangular src3182) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3182_2393 : (Triangular src3182) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3182_2399 : (Triangular src3182) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3182_2415 : (Triangular src3182) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3182_2458 : (Triangular src3182) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3182 : Cover (Triangular src3182) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass3182_2390, by decide, by decide, pass3182_2391, by decide, by decide, pass3182_2393, by decide, by decide, pass3182_2399, by decide, by decide, pass3182_2415, by decide, by decide, pass3182_2458, rfl⟩
def src3183 : Request := ⟨⟨⟨1750,2439,537,35878⟩,163381988556800,985665319192⟩,85,7,1,899758,16⟩
private theorem pass3183_2390 : (Triangular src3183) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3183_2391 : (Triangular src3183) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3183_2393 : (Triangular src3183) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3183_2398 : (Triangular src3183) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3183_2412 : (Triangular src3183) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3183_2449 : (Triangular src3183) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3183 : Cover (Triangular src3183) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass3183_2390, by decide, by decide, pass3183_2391, by decide, by decide, pass3183_2393, by decide, by decide, pass3183_2398, by decide, by decide, pass3183_2412, by decide, by decide, pass3183_2449, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2164

-- Source: Research6969.PrefixRescueDataMiddle20
section Z6969Source2165
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle20
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,7,1,15⟩
  bank i := ![bank101 3537, bank100 3896, bank100 4596, bank143 6108, bank202 10158, bank247 25686, bank217 31947, bank336 68638, bank294 118544, bank305 174005] i
  reserve i := ![0, 1, 3, 8, 20, 65, 50, 190, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 9

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 3537
    · exact rank100 3896
    · exact rank100 4596
    · exact rank143 6108
    · exact rank202 10158
    · exact rank247 25686
    · exact rank217 31947
    · exact rank336 68638
    · exact rank294 118544
    · exact rank305 174005
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3166⟩
    · exact ⟨_, cover3167⟩
    · exact ⟨_, cover3168⟩
    · exact ⟨_, cover3169⟩
    · exact ⟨_, cover3170⟩
    · exact ⟨_, cover3172⟩
    · exact ⟨_, cover3171⟩
    · exact ⟨_, cover3174⟩
    · exact ⟨_, cover3173⟩
    · exact ⟨_, cover3175⟩

def price : EarlyPrice := ⟨7, 15, 9, 85/100, 70/100, ![1017187988700, 431778917905, 10230045000, 4092026750], 579395068129230⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6484/123, 94888/191, 599686/191, 1029570/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle20
end Z6969Source2165

-- Source: Research6969.PrefixMiddleSaved20
section Z6969Source2166
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved20
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle20.price Lower6960.Prefix6969RescueData.Middle20.price :=
  ⟨342, 3665, 52, 496, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle20.plan Lower6960.Prefix6969RescueData.Middle20.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 7 9 15 :=
  ⟨Lower6960.Prefix6969MainCases.Middle20.plan, Lower6960.Prefix6969MainCases.Middle20.price, Lower6960.Prefix6969MainCases.Middle20.valid, Lower6960.Prefix6969MainCases.Middle20.priced, Lower6960.Prefix6969MainCases.Middle20.sources,
   Lower6960.Prefix6969RescueData.Middle20.plan, Lower6960.Prefix6969RescueData.Middle20.price, Lower6960.Prefix6969RescueData.Middle20.sources, Lower6960.Prefix6969RescueData.Middle20.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved20
end Z6969Source2166

-- Source: Research6969.PrefixMainDataMiddle21
section Z6969Source2167
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle21
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 13, 15, 21, 21, 30, 40, 40, 65, 75, 75, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank19 1276, bank24 1404, bank33 1472, bank42 1693, bank55 1948, bank72 2320, bank65 2772, bank123 3043, bank89 3630, bank168 3916, bank124 10359, bank147 5174, bank199 7608, bank211 8704, bank187 16602, bank172 23613, bank171 27879] i
  head := src3220
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15815, 124768, 573786, 1978936],
    ![24861/2, 91197, 831651/2, 1454436],
    ![6218, 398878/9, 831651/2, 1415722],
    ![29433/8, 214757/8, 1944860/9, 692328],
    ![65616/25, 463264/25, 158976, 541696],
    ![73478/49, 527462/49, 2376554/25, 2866249/9],
    ![45497/50, 314253/50, 72563, 237169],
    ![45497/50, 314253/50, 1714331/25, 215296],
    ![13307/16, 314253/50, 7386568/121, 213444],
    ![84176/121, 543193/121, 2363982/49, 964631/7],
    ![66774/121, 543193/121, 745965/16, 964631/7],
    ![66774/121, 543193/121, 745965/16, 126736],
    ![20667/50, 543193/121, 745965/16, 126736],
    ![20667/50, 101018/25, 1914380/49, 91848848/729],
    ![20667/50, 538900/147, 1490217/44, 57881664/529],
    ![20667/50, 19180504/5329, 86397038/2601, 67599616/625],
    ![1960504/5329, 19180504/5329, 86397038/2601, 67599616/625],
    ![1872696/5329, 19180504/5329, 86397038/2601, 67599616/625],
    ![1826342/5329, 19180504/5329, 86397038/2601, 67599616/625]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 16 899758 := by
  refine ⟨?_, rank154 4438, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3220⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free19_1
    · exact free24_1
    · exact free33_2
    · exact free42_3
    · exact free55_1
    · exact free72_1
    · exact free65_1
    · exact free123_1
    · exact free89_4
    · exact free168_1
    · exact free124_1
    · exact free147_1
    · exact free199_1
    · exact free211_1
    · exact free187_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [242840926, 308003674, 307513234, 308609987, 308814805, 308803959, 147057977, 147136234, 147113516, 71548375, 102929134, 62660865, 55000000, 65451858, 93577248, 93965627, 98114393, 100000000, 223636516], [1508696, 1150628, 1153139, 1147523, 1146474, 1146529, 2618635, 2617332, 2617710, 5609137, 3835190, 6431043, 7352332, 6144660, 4239542, 4219936, 4038618, 3958949, 1666762],
  ![118710735423120, 1619172923384, 201272864400, 6267553200], 131228083721559627⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 19180504/5329, 86397038/2601, 67599616/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle21
end Z6969Source2167

end Merged_Z6969Pack0759

-- merged module Z6969Pack0760
section Merged_Z6969Pack0760

-- Source: Research6969.PhysicalChecks199
section Z6969Source2168
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src3184 : Request := ⟨⟨⟨3950,5507,1244,46448⟩,1913299978158080,26084011577468⟩,145,7,1,899758,16⟩
private theorem pass3184_2390 : (Triangular src3184) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3184_2391 : (Triangular src3184) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3184_2393 : (Triangular src3184) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3184_2398 : (Triangular src3184) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3184_2411 : (Triangular src3184) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3184_2445 : (Triangular src3184) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3184_2533 : (Triangular src3184) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3184 : Cover (Triangular src3184) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3184_2390, by decide, by decide, pass3184_2391, by decide, by decide, pass3184_2393, by decide, by decide, pass3184_2398, by decide, by decide, pass3184_2411, by decide, by decide, pass3184_2445, by decide, by decide, pass3184_2533, rfl⟩
def src3185 : Request := ⟨⟨⟨3200,4459,1008,104380⟩,1017717693874176,11221829825062⟩,190,7,1,899758,16⟩
private theorem pass3185_2390 : (Triangular src3185) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3185_2391 : (Triangular src3185) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3185_2393 : (Triangular src3185) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3185_2398 : (Triangular src3185) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3185_2411 : (Triangular src3185) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3185_2445 : (Triangular src3185) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3185_2534 : (Triangular src3185) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3185 : Cover (Triangular src3185) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3185_2390, by decide, by decide, pass3185_2391, by decide, by decide, pass3185_2393, by decide, by decide, pass3185_2398, by decide, by decide, pass3185_2411, by decide, by decide, pass3185_2445, by decide, by decide, pass3185_2534, rfl⟩
def src3186 : Request := ⟨⟨⟨6900,9621,2174,76395⟩,10196763128627200,242895948111878⟩,245,7,1,899758,16⟩
private theorem pass3186_2390 : (Triangular src3186) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3186_2391 : (Triangular src3186) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3186_2393 : (Triangular src3186) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3186_2398 : (Triangular src3186) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3186_2411 : (Triangular src3186) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3186_2445 : (Triangular src3186) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3186_2532 : (Triangular src3186) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3186 : Cover (Triangular src3186) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass3186_2390, by decide, by decide, pass3186_2391, by decide, by decide, pass3186_2393, by decide, by decide, pass3186_2398, by decide, by decide, pass3186_2411, by decide, by decide, pass3186_2445, by decide, by decide, pass3186_2532, rfl⟩
def src3187 : Request := ⟨⟨⟨225,314,69,2653⟩,353440890880,276676118⟩,0,7,1,899758,26⟩
private theorem pass3187_2390 : (Triangular src3187) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3187_2391 : (Triangular src3187) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3187_2394 : (Triangular src3187) 2394 2404 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3187_2405 : (Triangular src3187) 2405 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3187_2445 : (Triangular src3187) 2445 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3187 : Cover (Triangular src3187) 2534 2390 [2390,2393,2404,2444,2534] := by
  exact ⟨by decide, by decide, pass3187_2390, by decide, by decide, pass3187_2391, by decide, by decide, pass3187_2394, by decide, by decide, pass3187_2405, by decide, by decide, pass3187_2445, rfl⟩
def src3188 : Request := ⟨⟨⟨275,383,83,2891⟩,635228389376,603020643⟩,1,7,1,899758,26⟩
private theorem pass3188_2390 : (Triangular src3188) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3188_2391 : (Triangular src3188) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3188_2394 : (Triangular src3188) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3188_2404 : (Triangular src3188) 2404 2438 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3188_2439 : (Triangular src3188) 2439 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3188 : Cover (Triangular src3188) 2534 2390 [2390,2393,2403,2438,2534] := by
  exact ⟨by decide, by decide, pass3188_2390, by decide, by decide, pass3188_2391, by decide, by decide, pass3188_2394, by decide, by decide, pass3188_2404, by decide, by decide, pass3188_2439, rfl⟩
def src3189 : Request := ⟨⟨⟨325,453,100,3339⟩,1061047500800,1193036697⟩,3,7,1,899758,26⟩
private theorem pass3189_2390 : (Triangular src3189) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3189_2391 : (Triangular src3189) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3189_2394 : (Triangular src3189) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3189_2404 : (Triangular src3189) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3189_2436 : (Triangular src3189) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3189 : Cover (Triangular src3189) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass3189_2390, by decide, by decide, pass3189_2391, by decide, by decide, pass3189_2394, by decide, by decide, pass3189_2404, by decide, by decide, pass3189_2436, rfl⟩
def src3190 : Request := ⟨⟨⟨400,558,123,4125⟩,1971918995456,2734096379⟩,6,7,1,899758,26⟩
private theorem pass3190_2390 : (Triangular src3190) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3190_2391 : (Triangular src3190) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3190_2394 : (Triangular src3190) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3190_2403 : (Triangular src3190) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3190_2431 : (Triangular src3190) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3190_2517 : (Triangular src3190) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3190 : Cover (Triangular src3190) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass3190_2390, by decide, by decide, pass3190_2391, by decide, by decide, pass3190_2394, by decide, by decide, pass3190_2403, by decide, by decide, pass3190_2431, by decide, by decide, pass3190_2517, rfl⟩
def src3191 : Request := ⟨⟨⟨560,781,172,5942⟩,5388141854720,10440670587⟩,13,7,1,899758,26⟩
private theorem pass3191_2390 : (Triangular src3191) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3191_2391 : (Triangular src3191) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3191_2393 : (Triangular src3191) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3191_2399 : (Triangular src3191) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3191_2417 : (Triangular src3191) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3191_2469 : (Triangular src3191) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3191 : Cover (Triangular src3191) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass3191_2390, by decide, by decide, pass3191_2391, by decide, by decide, pass3191_2393, by decide, by decide, pass3191_2399, by decide, by decide, pass3191_2417, by decide, by decide, pass3191_2469, rfl⟩
def src3192 : Request := ⟨⟨⟨1000,1394,307,10864⟩,30557599170560,105471636407⟩,32,7,1,899758,26⟩
private theorem pass3192_2390 : (Triangular src3192) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3192_2391 : (Triangular src3192) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3192_2393 : (Triangular src3192) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3192_2399 : (Triangular src3192) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3192_2415 : (Triangular src3192) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3192_2459 : (Triangular src3192) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3192 : Cover (Triangular src3192) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass3192_2390, by decide, by decide, pass3192_2391, by decide, by decide, pass3192_2393, by decide, by decide, pass3192_2399, by decide, by decide, pass3192_2415, by decide, by decide, pass3192_2459, rfl⟩
def src3193 : Request := ⟨⟨⟨2600,3624,798,32048⟩,535425056505856,4799424311630⟩,110,7,1,899758,26⟩
private theorem pass3193_2390 : (Triangular src3193) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3193_2391 : (Triangular src3193) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3193_2393 : (Triangular src3193) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3193_2398 : (Triangular src3193) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3193_2411 : (Triangular src3193) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3193_2446 : (Triangular src3193) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3193 : Cover (Triangular src3193) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass3193_2390, by decide, by decide, pass3193_2391, by decide, by decide, pass3193_2393, by decide, by decide, pass3193_2398, by decide, by decide, pass3193_2411, by decide, by decide, pass3193_2446, rfl⟩
def src3194 : Request := ⟨⟨⟨2600,3623,819,56773⟩,546063062138880,4892906717079⟩,145,7,1,899758,26⟩
private theorem pass3194_2390 : (Triangular src3194) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3194_2391 : (Triangular src3194) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3194_2393 : (Triangular src3194) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3194_2398 : (Triangular src3194) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3194_2411 : (Triangular src3194) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3194_2445 : (Triangular src3194) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3194_2534 : (Triangular src3194) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3194 : Cover (Triangular src3194) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3194_2390, by decide, by decide, pass3194_2391, by decide, by decide, pass3194_2393, by decide, by decide, pass3194_2398, by decide, by decide, pass3194_2411, by decide, by decide, pass3194_2445, by decide, by decide, pass3194_2534, rfl⟩
def src3195 : Request := ⟨⟨⟨3200,4459,1008,85010⟩,1017717693874176,11221829825062⟩,190,7,1,899758,26⟩
private theorem pass3195_2390 : (Triangular src3195) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3195_2391 : (Triangular src3195) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3195_2393 : (Triangular src3195) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3195_2398 : (Triangular src3195) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3195_2411 : (Triangular src3195) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3195_2445 : (Triangular src3195) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3195_2534 : (Triangular src3195) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3195 : Cover (Triangular src3195) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass3195_2390, by decide, by decide, pass3195_2391, by decide, by decide, pass3195_2393, by decide, by decide, pass3195_2398, by decide, by decide, pass3195_2411, by decide, by decide, pass3195_2445, by decide, by decide, pass3195_2534, rfl⟩
def src3196 : Request := ⟨⟨⟨4800,6692,1512,50693⟩,3433136573644800,56871238465897⟩,190,7,1,899758,26⟩
private theorem pass3196_2390 : (Triangular src3196) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3196_2391 : (Triangular src3196) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3196_2393 : (Triangular src3196) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3196_2398 : (Triangular src3196) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3196_2411 : (Triangular src3196) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3196_2445 : (Triangular src3196) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3196_2533 : (Triangular src3196) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3196 : Cover (Triangular src3196) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3196_2390, by decide, by decide, pass3196_2391, by decide, by decide, pass3196_2393, by decide, by decide, pass3196_2398, by decide, by decide, pass3196_2411, by decide, by decide, pass3196_2445, by decide, by decide, pass3196_2533, rfl⟩
def src3197 : Request := ⟨⟨⟨3950,5504,1244,124298⟩,1913299978158080,26038250013848⟩,245,7,1,899758,26⟩
private theorem pass3197_2390 : (Triangular src3197) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3197_2391 : (Triangular src3197) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3197_2393 : (Triangular src3197) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3197_2398 : (Triangular src3197) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3197_2411 : (Triangular src3197) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3197_2445 : (Triangular src3197) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3197_2533 : (Triangular src3197) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3197 : Cover (Triangular src3197) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass3197_2390, by decide, by decide, pass3197_2391, by decide, by decide, pass3197_2393, by decide, by decide, pass3197_2398, by decide, by decide, pass3197_2411, by decide, by decide, pass3197_2445, by decide, by decide, pass3197_2533, rfl⟩
def src3198 : Request := ⟨⟨⟨225,314,68,2104⟩,349597597696,273591980⟩,0,7,1,899758,41⟩
private theorem pass3198_2390 : (Triangular src3198) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3198_2391 : (Triangular src3198) 2391 2394 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3198_2395 : (Triangular src3198) 2395 2408 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3198_2409 : (Triangular src3198) 2409 2460 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3198_2461 : (Triangular src3198) 2461 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3198 : Cover (Triangular src3198) 2534 2390 [2390,2394,2408,2460,2534] := by
  exact ⟨by decide, by decide, pass3198_2390, by decide, by decide, pass3198_2391, by decide, by decide, pass3198_2395, by decide, by decide, pass3198_2409, by decide, by decide, pass3198_2461, rfl⟩
def src3199 : Request := ⟨⟨⟨275,383,83,2284⟩,635228389376,603020643⟩,1,7,1,899758,41⟩
private theorem pass3199_2390 : (Triangular src3199) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3199_2391 : (Triangular src3199) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3199_2394 : (Triangular src3199) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3199_2404 : (Triangular src3199) 2404 2438 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass3199_2439 : (Triangular src3199) 2439 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover3199 : Cover (Triangular src3199) 2534 2390 [2390,2393,2403,2438,2534] := by
  exact ⟨by decide, by decide, pass3199_2390, by decide, by decide, pass3199_2391, by decide, by decide, pass3199_2394, by decide, by decide, pass3199_2404, by decide, by decide, pass3199_2439, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2168

-- Source: Research6969.PrefixRescueDataMiddle21
section Z6969Source2169
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle21
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,25⟩
  bank i := ![bank101 3154, bank100 3473, bank100 3755, bank134 4298, bank143 5427, bank193 7913, bank224 15403, bank239 35878, bank307 46448, bank294 104380, bank350 76395] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 85, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 16

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 3154
    · exact rank100 3473
    · exact rank100 3755
    · exact rank134 4298
    · exact rank143 5427
    · exact rank193 7913
    · exact rank224 15403
    · exact rank239 35878
    · exact rank307 46448
    · exact rank294 104380
    · exact rank350 76395
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3176⟩
    · exact ⟨_, cover3177⟩
    · exact ⟨_, cover3178⟩
    · exact ⟨_, cover3179⟩
    · exact ⟨_, cover3180⟩
    · exact ⟨_, cover3181⟩
    · exact ⟨_, cover3182⟩
    · exact ⟨_, cover3183⟩
    · exact ⟨_, cover3184⟩
    · exact ⟨_, cover3185⟩
    · exact ⟨_, cover3186⟩

def price : EarlyPrice := ⟨7, 25, 10, 75/100, 70/100, ![1016963588860, 277694595927, 21181058078, 5083466374], 619403807621311⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![10507/191, 38774/73, 129215/41, 636625/82] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle21
end Z6969Source2169

-- Source: Research6969.PrefixMiddleSaved21
section Z6969Source2170
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved21
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle21.price Lower6960.Prefix6969RescueData.Middle21.price :=
  ⟨342, 3599, 55, 531, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle21.plan Lower6960.Prefix6969RescueData.Middle21.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 7 16 25 :=
  ⟨Lower6960.Prefix6969MainCases.Middle21.plan, Lower6960.Prefix6969MainCases.Middle21.price, Lower6960.Prefix6969MainCases.Middle21.valid, Lower6960.Prefix6969MainCases.Middle21.priced, Lower6960.Prefix6969MainCases.Middle21.sources,
   Lower6960.Prefix6969RescueData.Middle21.plan, Lower6960.Prefix6969RescueData.Middle21.price, Lower6960.Prefix6969RescueData.Middle21.sources, Lower6960.Prefix6969RescueData.Middle21.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved21
end Z6969Source2170

-- Source: Research6969.PrefixMainDataMiddle22
section Z6969Source2171
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle22
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 19
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 13, 15, 21, 18, 21, 25, 30, 40, 40, 65, 75, 75] i
  bank i := ![bank3 1102, bank11 1192, bank19 1276, bank24 1404, bank33 1472, bank37 1587, bank45 1806, bank61 2044, bank72 2320, bank65 2772, bank89 3630, bank103 2789, bank123 3043, bank140 3403, bank168 3916, bank122 10626, bank159 5020, bank199 7608, bank172 23613, bank171 27879] i
  head := src3221
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  historyValues := [![15751, 123092, 562300, 1933342],
    ![12581, 88659, 399511, 1420864],
    ![6218, 385348/9, 399511, 1310452],
    ![29433/8, 103831/4, 1880840/9, 640848],
    ![65616/25, 447424/25, 158976, 541696],
    ![17323/9, 79883/6, 134855, 1629849/4],
    ![38747/32, 67647/8, 2437664/25, 7419048/25],
    ![96292/121, 639148/121, 58612, 1199536/7],
    ![96292/121, 639148/121, 58612, 1199536/7],
    ![96292/121, 639148/121, 58612, 1199536/7],
    ![66774/121, 544708/121, 2245374/49, 1464100/9],
    ![66774/121, 544708/121, 2245374/49, 7778521/49],
    ![66774/121, 523393/121, 2245374/49, 6250322/49],
    ![66774/121, 523393/121, 2245374/49, 6250322/49],
    ![66774/121, 523393/121, 2245374/49, 3016299/25],
    ![41249/100, 523393/121, 2245374/49, 3016299/25],
    ![41249/100, 15723/4, 28335152/729, 82488640/729],
    ![41249/100, 173400/49, 17331024/529, 187521984/1849],
    ![1872696/5329, 173400/49, 17331024/529, 187521984/1849],
    ![1826342/5329, 173400/49, 17331024/529, 187521984/1849]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 26 899758 := by
  refine ⟨?_, rank154 4108, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3221⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free11_1
    · exact free19_1
    · exact free24_1
    · exact free33_2
    · exact free37_1
    · exact free45_1
    · exact free61_1
    · exact free72_1
    · exact free65_1
    · exact free89_4
    · exact free103_2
    · exact free123_1
    · exact free140_1
    · exact free168_1
    · exact free122_1
    · exact free159_1
    · exact free199_1
    · exact free172_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [234397492, 296797354, 296738057, 297292253, 297416183, 297094483, 296447619, 107111453, 96432914, 89438481, 88432020, 88287915, 103734583, 103691750, 64285048, 67236324, 94030305, 109182758, 136276803, 223028361], [1578192, 1208019, 1208323, 1205485, 1204850, 1206497, 1209810, 3682289, 4109662, 4448474, 4499282, 4506557, 3801159, 3802968, 6264386, 5981483, 4216671, 3610307, 2854668, 1671768],
  ![118387914586020, 1619833027284, 200725524900, 4301004420], 125906020643109481⟩

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
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 173400/49, 17331024/529, 187521984/1849] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle22
end Z6969Source2171

-- Source: Research6969.PrefixRescueDataMiddle22
section Z6969Source2172
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle22
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,40⟩
  bank i := ![bank60 2653, bank78 2891, bank101 3339, bank134 4125, bank156 5942, bank218 10864, bank260 32048, bank259 56773, bank320 50693, bank305 124298, bank294 85010] i
  reserve i := ![0, 1, 3, 6, 13, 32, 110, 145, 190, 245, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 26

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank60 2653
    · exact rank78 2891
    · exact rank101 3339
    · exact rank134 4125
    · exact rank156 5942
    · exact rank218 10864
    · exact rank260 32048
    · exact rank259 56773
    · exact rank320 50693
    · exact rank305 124298
    · exact rank294 85010
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3187⟩
    · exact ⟨_, cover3188⟩
    · exact ⟨_, cover3189⟩
    · exact ⟨_, cover3190⟩
    · exact ⟨_, cover3191⟩
    · exact ⟨_, cover3192⟩
    · exact ⟨_, cover3193⟩
    · exact ⟨_, cover3194⟩
    · exact ⟨_, cover3196⟩
    · exact ⟨_, cover3197⟩
    · exact ⟨_, cover3195⟩

def price : EarlyPrice := ⟨7, 40, 10, 70/100, 70/100, ![1937635780336, 357053710018, 23570011584, 3535511112], 748140348486979⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6484/123, 63968/111, 622531/191, 2027720/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle22
end Z6969Source2172

-- Source: Research6969.PrefixMiddleSaved22
section Z6969Source2173
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved22
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle22.price Lower6960.Prefix6969RescueData.Middle22.price :=
  ⟨342, 3538, 52, 576, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle22.plan Lower6960.Prefix6969RescueData.Middle22.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 7 26 40 :=
  ⟨Lower6960.Prefix6969MainCases.Middle22.plan, Lower6960.Prefix6969MainCases.Middle22.price, Lower6960.Prefix6969MainCases.Middle22.valid, Lower6960.Prefix6969MainCases.Middle22.priced, Lower6960.Prefix6969MainCases.Middle22.sources,
   Lower6960.Prefix6969RescueData.Middle22.plan, Lower6960.Prefix6969RescueData.Middle22.price, Lower6960.Prefix6969RescueData.Middle22.sources, Lower6960.Prefix6969RescueData.Middle22.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved22
end Z6969Source2173

-- Source: Research6969.PrefixMainDataMiddle25
section Z6969Source2174
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle25
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 18, 21, 65, 75, 75] i
  bank i := ![bank3 1102, bank11 1192, bank19 1276, bank24 1404, bank37 1587, bank50 1914, bank63 2304, bank89 2959, bank123 3043, bank167 13649, bank215 8473, bank171 27879] i
  head := src3222
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![15999, 122301, 560552, 1891334],
    ![12581, 169955/2, 393360, 1420864],
    ![6218, 123010/3, 393360, 1183490],
    ![29433/8, 199105/8, 1803628/9, 578760],
    ![17323/9, 12750, 1033667/8, 2943885/8],
    ![81680/81, 182660/27, 617972/9, 915849/4],
    ![81680/81, 182660/27, 617972/9, 5308416/25],
    ![250508/361, 1688700/361, 2432298/49, 5488945/36],
    ![250508/361, 499513/121, 2168878/49, 806395/7],
    ![55840/147, 499513/121, 22466254/529, 806395/7],
    ![55840/147, 17847900/5329, 40254991/1250, 4490690/49],
    ![1826342/5329, 17847900/5329, 40254991/1250, 4490690/49]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 7 41 899758 := by
  refine ⟨?_, rank154 3710, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover3222⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free11_1
    · exact free19_1
    · exact free24_1
    · exact free37_1
    · exact free50_1
    · exact free63_1
    · exact free89_3
    · exact free123_1
    · exact free167_1
    · exact free215_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [228275332, 288787889, 288382082, 288585773, 288405855, 152048894, 152076826, 152011655, 75505992, 95395549, 96732670, 221903722], [1628581, 1249038, 1251117, 1250073, 1250995, 2535564, 2535099, 2536184, 5302015, 4153492, 4096997, 1681024],
  ![117790933712040, 1621052982728, 199713349800, 5408055300], 121955046806710743⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 17847900/5329, 40254991/1250, 4490690/49] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle25
end Z6969Source2174

-- Source: Research6969.PrefixRescueDataMiddle25
section Z6969Source2175
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle25
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,56⟩
  bank i := ![bank59 2104, bank78 2284, bank78 2499, bank100 2931, bank134 3697, bank193 6110, bank225 12583, bank295 32563, bank294 59468, bank335 51085, bank305 85612] i
  reserve i := ![0, 1, 2, 4, 8, 20, 50, 145, 190, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 899758
  seedFloor := 41

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank59 2104
    · exact rank78 2284
    · exact rank78 2499
    · exact rank100 2931
    · exact rank134 3697
    · exact rank193 6110
    · exact rank225 12583
    · exact rank295 32563
    · exact rank294 59468
    · exact rank335 51085
    · exact rank305 85612
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover3198⟩
    · exact ⟨_, cover3199⟩
    · exact ⟨_, cover3200⟩
    · exact ⟨_, cover3201⟩
    · exact ⟨_, cover3202⟩
    · exact ⟨_, cover3203⟩
    · exact ⟨_, cover3204⟩
    · exact ⟨_, cover3205⟩
    · exact ⟨_, cover3206⟩
    · exact ⟨_, cover3208⟩
    · exact ⟨_, cover3207⟩

def price : EarlyPrice := ⟨7, 56, 10, 65/100, 60/100, ![1868403393796, 293157218792, 39196053068, 4199588596], 805384295608280⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6484/123, 87555/146, 802571/246, 1430380/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle25
end Z6969Source2175

-- Source: Research6969.PrefixMiddleSaved25
section Z6969Source2176
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved25
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle25.price Lower6960.Prefix6969RescueData.Middle25.price :=
  ⟨342, 3349, 52, 599, true⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle25.plan Lower6960.Prefix6969RescueData.Middle25.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    exact ⟨by decide, by decide +kernel⟩
  · rw [Budget.extra, Budget.adjust]
    decide +kernel

def data : Case 7 41 56 :=
  ⟨Lower6960.Prefix6969MainCases.Middle25.plan, Lower6960.Prefix6969MainCases.Middle25.price, Lower6960.Prefix6969MainCases.Middle25.valid, Lower6960.Prefix6969MainCases.Middle25.priced, Lower6960.Prefix6969MainCases.Middle25.sources,
   Lower6960.Prefix6969RescueData.Middle25.plan, Lower6960.Prefix6969RescueData.Middle25.price, Lower6960.Prefix6969RescueData.Middle25.sources, Lower6960.Prefix6969RescueData.Middle25.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved25
end Z6969Source2176

-- Source: Research6969.PrefixMiddleSelect7
section Z6969Source2177
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer
set_option maxHeartbeats 8000000

theorem choose7 (j : Fin 56) :
    ∃ l u : ℕ, l≤j.val+1 ∧ j.val+1≤u ∧ Nonempty (Case 7 l u) := by
  fin_cases j
  · exact ⟨1, 1, by decide, by decide, ⟨Saved17.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved18.data⟩⟩
  · exact ⟨2, 3, by decide, by decide, ⟨Saved18.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved19.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved19.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved19.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved19.data⟩⟩
  · exact ⟨4, 8, by decide, by decide, ⟨Saved19.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨9, 15, by decide, by decide, ⟨Saved20.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨16, 25, by decide, by decide, ⟨Saved21.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨26, 40, by decide, by decide, ⟨Saved22.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩
  · exact ⟨41, 56, by decide, by decide, ⟨Saved25.data⟩⟩

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source2177

-- Source: Research6969.PrefixMiddleRoute
section Z6969Source2178
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969MiddleTransfer
open Finset Polynomial
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family)
open Research6966

theorem choose (a : Fin 6) (s : Fin 56) :
    ∃ l u : ℕ, l≤s.val+1 ∧ s.val+1≤u ∧ Nonempty (Case (a.val+2) l u) := by
  fin_cases a
  · exact choose2 s
  · exact choose3 s
  · exact choose4 s
  · exact choose5 s
  · exact choose6 s
  · exact choose7 s

/-- At the actual middle model, exhaust the unit, affine and every
nonlinear outer-helper interval, producing the common terminal input. -/
theorem route {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2390≤M.overhead.toNat) (hi : M.overhead.toNat≤2534)
    (noPole : ∀j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Packet F Crt) :=
  route_using choose F Crt lo hi noPole residues

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source2178

-- Source: Research6969.MiddleBand
section Z6969Source2179
set_option autoImplicit true
namespace Research6969.MiddleBand
open Lower6960
open Far6969RescueGeometry (Model Family)

/-- Unconditional model-level bound throughout the second transition interval. -/
theorem count {u del} (M:Model u del) {Γ} (F:Family M Γ)
    (lo:2390≤M.overhead) (hi:M.overhead≤2534):Γ.card≤274784969259510674 :=
  MiddleBudget.from_router M F lo hi (fun Crt=>Prefix6969MiddleTransfer.route F Crt (by omega) (by omega))

end Research6969.MiddleBand
end Z6969Source2179

end Merged_Z6969Pack0760

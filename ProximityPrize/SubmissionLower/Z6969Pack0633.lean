import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- Source: Research6969.PrefixMainDataHighQuadraticFinal9
section Z6969Source0809
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal9
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank144 4704, bank150 6517, bank120 36262, bank198 9780, bank210 11036, bank183 54742, bank174 148759, bank169 292467] i
  head := src1195
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 169611, 789260, 4134723],
    ![12303, 137663, 1244651/2, 3096562],
    ![53398/9, 596653/9, 619520, 3096562],
    ![29433/8, 640421/16, 2898574/9, 14018426/9],
    ![16211/9, 246593/12, 3371401/16, 17107361/16],
    ![24292/27, 912361/81, 4145615/36, 22797103/36],
    ![73478/121, 1185698/121, 5352251/49, 22797103/36],
    ![73478/121, 1185698/121, 5352251/49, 9465107/18],
    ![73478/121, 972637/121, 4360297/49, 19342072/49],
    ![63754/121, 3218858/441, 543881/8, 19342072/49],
    ![63754/121, 3218858/441, 543881/8, 44282362/121],
    ![61324/121, 3218858/441, 543881/8, 44282362/121],
    ![61324/121, 778469/121, 13456028/225, 56683864/225],
    ![61324/121, 778469/121, 1243349/21, 26908056/121],
    ![61324/121, 9587412/1681, 43158036/841, 26908056/121],
    ![667406/1681, 9587412/1681, 43158036/841, 26908056/121],
    ![667406/1681, 7016668/1323, 31559386/675, 10627600/49],
    ![667406/1681, 7020440/1369, 126374794/2809, 589201004/2809],
    ![954471/2738, 7020440/1369, 126374794/2809, 589201004/2809],
    ![462882/1369, 7020440/1369, 126374794/2809, 589201004/2809],
    ![459151/1369, 7020440/1369, 126374794/2809, 589201004/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 11 308063 := by
  refine ⟨?_, rank154 7627, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1195⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free144_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free210_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [347237618, 345737371, 346866748, 345292806, 345345864, 346411895, 345454338, 346601321, 167393660, 167913672, 168100202, 167868382, 115705130, 74375446, 67007639, 91113394, 105978186, 105482226, 127004852, 174035264, 235363704], [994832, 998944, 995849, 1000162, 1000017, 997095, 999720, 996576, 2277686, 2269040, 2265939, 2269793, 3383565, 5378361, 5995716, 4359185, 3717633, 3734850, 3067691, 2183607, 1568535],
  ![124935761357280, 1605544152636, 211827333600, 4446368700], 191189708424265424⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7020440/1369, 126374794/2809, 589201004/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal9
end Z6969Source0809

-- Source: Research6969.PhysicalChecks052
section Z6969Source0810
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src504 : Request := ⟨⟨⟨2600,3628,783,264035⟩,527755772952576,4745819470168⟩,13,2,1,307921,13⟩
private theorem pass504_2293 : (Triangular src504) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass504_2295 : (Triangular src504) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass504_2301 : (Triangular src504) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass504_2317 : (Triangular src504) 2317 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass504_2362 : (Triangular src504) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover504 : Cover (Triangular src504) 2389 2293 [2294,2300,2316,2361,2389] := by
  exact ⟨by decide, by decide, pass504_2293, by decide, by decide, pass504_2295, by decide, by decide, pass504_2301, by decide, by decide, pass504_2317, by decide, by decide, pass504_2362, rfl⟩
def src505 : Request := ⟨⟨⟨3950,5512,1189,208621⟩,1848744952463360,25255771038451⟩,16,2,1,307921,13⟩
private theorem pass505_2293 : (Triangular src505) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass505_2295 : (Triangular src505) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass505_2300 : (Triangular src505) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass505_2314 : (Triangular src505) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass505_2353 : (Triangular src505) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover505 : Cover (Triangular src505) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass505_2293, by decide, by decide, pass505_2295, by decide, by decide, pass505_2300, by decide, by decide, pass505_2314, by decide, by decide, pass505_2353, rfl⟩
def src506 : Request := ⟨⟨⟨4800,6698,1445,234698⟩,3317023033262080,55058665830093⟩,20,2,1,307921,13⟩
private theorem pass506_2293 : (Triangular src506) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass506_2294 : (Triangular src506) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass506_2297 : (Triangular src506) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass506_2305 : (Triangular src506) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass506_2327 : (Triangular src506) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass506_2388 : (Triangular src506) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover506 : Cover (Triangular src506) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass506_2293, by decide, by decide, pass506_2294, by decide, by decide, pass506_2297, by decide, by decide, pass506_2305, by decide, by decide, pass506_2327, by decide, by decide, pass506_2388, rfl⟩
def src507 : Request := ⟨⟨⟨3950,5512,1169,422931⟩,1824966114017280,24923274283249⟩,25,2,1,307921,13⟩
private theorem pass507_2293 : (Triangular src507) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass507_2294 : (Triangular src507) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass507_2296 : (Triangular src507) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass507_2302 : (Triangular src507) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass507_2319 : (Triangular src507) 2319 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass507_2367 : (Triangular src507) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover507 : Cover (Triangular src507) 2389 2293 [2293,2295,2301,2318,2366,2389] := by
  exact ⟨by decide, by decide, pass507_2293, by decide, by decide, pass507_2294, by decide, by decide, pass507_2296, by decide, by decide, pass507_2302, by decide, by decide, pass507_2319, by decide, by decide, pass507_2367, rfl⟩
def src508 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,0,2,1,307995,12⟩
private theorem pass508_2293 : (Triangular src508) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass508_2298 : (Triangular src508) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass508_2312 : (Triangular src508) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass508_2352 : (Triangular src508) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover508 : Cover (Triangular src508) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass508_2293, by decide, by decide, pass508_2298, by decide, by decide, pass508_2312, by decide, by decide, pass508_2352, rfl⟩
def src509 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,1,2,1,307995,12⟩
private theorem pass509_2293 : (Triangular src509) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass509_2299 : (Triangular src509) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass509_2316 : (Triangular src509) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass509_2364 : (Triangular src509) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover509 : Cover (Triangular src509) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass509_2293, by decide, by decide, pass509_2299, by decide, by decide, pass509_2316, by decide, by decide, pass509_2364, rfl⟩
def src510 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,2,2,1,307995,12⟩
private theorem pass510_2293 : (Triangular src510) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass510_2298 : (Triangular src510) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass510_2312 : (Triangular src510) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass510_2352 : (Triangular src510) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover510 : Cover (Triangular src510) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass510_2293, by decide, by decide, pass510_2298, by decide, by decide, pass510_2312, by decide, by decide, pass510_2352, rfl⟩
def src511 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,3,2,1,307995,12⟩
private theorem pass511_2293 : (Triangular src511) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass511_2296 : (Triangular src511) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass511_2305 : (Triangular src511) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass511_2331 : (Triangular src511) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover511 : Cover (Triangular src511) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass511_2293, by decide, by decide, pass511_2296, by decide, by decide, pass511_2305, by decide, by decide, pass511_2331, rfl⟩
def src512 : Request := ⟨⟨⟨1750,2442,527,146522⟩,161065121873920,975196209190⟩,4,2,1,307995,12⟩
private theorem pass512_2293 : (Triangular src512) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass512_2294 : (Triangular src512) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass512_2297 : (Triangular src512) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass512_2305 : (Triangular src512) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass512_2328 : (Triangular src512) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover512 : Cover (Triangular src512) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass512_2293, by decide, by decide, pass512_2294, by decide, by decide, pass512_2297, by decide, by decide, pass512_2305, by decide, by decide, pass512_2328, rfl⟩
def src513 : Request := ⟨⟨⟨2100,2930,632,164837⟩,278060332482560,2019119590628⟩,6,2,1,307995,12⟩
private theorem pass513_2293 : (Triangular src513) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass513_2297 : (Triangular src513) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass513_2309 : (Triangular src513) 2309 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass513_2343 : (Triangular src513) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover513 : Cover (Triangular src513) 2389 2293 [2296,2308,2342,2389] := by
  exact ⟨by decide, by decide, pass513_2293, by decide, by decide, pass513_2297, by decide, by decide, pass513_2309, by decide, by decide, pass513_2343, rfl⟩
def src514 : Request := ⟨⟨⟨2600,3628,783,164837⟩,527755772952576,4745819470168⟩,8,2,1,307995,12⟩
private theorem pass514_2293 : (Triangular src514) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass514_2296 : (Triangular src514) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass514_2304 : (Triangular src514) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass514_2327 : (Triangular src514) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover514 : Cover (Triangular src514) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass514_2293, by decide, by decide, pass514_2296, by decide, by decide, pass514_2304, by decide, by decide, pass514_2327, rfl⟩
def src515 : Request := ⟨⟨⟨3200,4465,947,185441⟩,970564165959680,10735676910569⟩,10,2,1,307995,12⟩
private theorem pass515_2293 : (Triangular src515) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass515_2295 : (Triangular src515) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass515_2301 : (Triangular src515) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass515_2318 : (Triangular src515) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass515_2366 : (Triangular src515) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover515 : Cover (Triangular src515) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass515_2293, by decide, by decide, pass515_2295, by decide, by decide, pass515_2301, by decide, by decide, pass515_2318, by decide, by decide, pass515_2366, rfl⟩
def src516 : Request := ⟨⟨⟨3200,4465,963,208621⟩,983050615259136,10877088344236⟩,13,2,1,307995,12⟩
private theorem pass516_2293 : (Triangular src516) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass516_2294 : (Triangular src516) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass516_2297 : (Triangular src516) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass516_2305 : (Triangular src516) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass516_2327 : (Triangular src516) 2327 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass516_2389 : (Triangular src516) 2389 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover516 : Cover (Triangular src516) 2389 2293 [2293,2296,2304,2326,2388,2389] := by
  exact ⟨by decide, by decide, pass516_2293, by decide, by decide, pass516_2294, by decide, by decide, pass516_2297, by decide, by decide, pass516_2305, by decide, by decide, pass516_2327, by decide, by decide, pass516_2389, rfl⟩
def src517 : Request := ⟨⟨⟨3950,5512,1189,297039⟩,1848744952463360,25255771038451⟩,20,2,1,307995,12⟩
private theorem pass517_2293 : (Triangular src517) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass517_2297 : (Triangular src517) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass517_2308 : (Triangular src517) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass517_2339 : (Triangular src517) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover517 : Cover (Triangular src517) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass517_2293, by decide, by decide, pass517_2297, by decide, by decide, pass517_2308, by decide, by decide, pass517_2339, rfl⟩
def src518 : Request := ⟨⟨⟨5700,7954,1716,297039⟩,5553838907981824,109473260530676⟩,25,2,1,307995,12⟩
private theorem pass518_2293 : (Triangular src518) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass518_2294 : (Triangular src518) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass518_2297 : (Triangular src518) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass518_2306 : (Triangular src518) 2306 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass518_2330 : (Triangular src518) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover518 : Cover (Triangular src518) 2389 2293 [2293,2296,2305,2329,2389] := by
  exact ⟨by decide, by decide, pass518_2293, by decide, by decide, pass518_2294, by decide, by decide, pass518_2297, by decide, by decide, pass518_2306, by decide, by decide, pass518_2330, rfl⟩
def src519 : Request := ⟨⟨⟨1450,2023,436,102908⟩,91566841790464,459151377566⟩,0,2,1,308063,11⟩
private theorem pass519_2293 : (Triangular src519) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass519_2296 : (Triangular src519) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass519_2304 : (Triangular src519) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass519_2327 : (Triangular src519) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover519 : Cover (Triangular src519) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass519_2293, by decide, by decide, pass519_2296, by decide, by decide, pass519_2304, by decide, by decide, pass519_2327, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source0810

-- Source: Research6969.PrefixNormalDataSeed11
section Z6969Source0811
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed11
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,11⟩
  bank i := ![bank236 102908, bank244 115771, bank251 130242, bank244 146522, bank245 164837, bank270 208621, bank303 185441, bank314 264035, bank331 297039, bank303 297039, bank347 334168] i
  reserve i := ![0, 1, 3, 3, 4, 10, 10, 16, 20, 16, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308063
  seedFloor := 11

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 102908
    · exact rank244 115771
    · exact rank251 130242
    · exact rank244 146522
    · exact rank245 164837
    · exact rank270 208621
    · exact rank303 185441
    · exact rank314 264035
    · exact rank331 297039
    · exact rank303 297039
    · exact rank347 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover519⟩
    · exact ⟨_, cover520⟩
    · exact ⟨_, cover522⟩
    · exact ⟨_, cover521⟩
    · exact ⟨_, cover523⟩
    · exact ⟨_, cover524⟩
    · exact ⟨_, cover525⟩
    · exact ⟨_, cover527⟩
    · exact ⟨_, cover528⟩
    · exact ⟨_, cover526⟩
    · exact ⟨_, cover529⟩

def price : NormalPrice := ⟨11, 95/100, 80/100, ![2273090674500, 220711052900, 7348298100, 668038800], 19509119143794733⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal9 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal9.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal9.price
    plan price SmallCertificates.primary11 SmallCertificates.rescue11 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 319
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 11))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 11 ≤ seedDegree G)
    (floor : 308063 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary11 SmallCertificates.rescue11) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal9.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal9.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal9.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 11))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 11 ≤ seedDegree G)
    (floor : 308063 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary11 SmallCertificates.rescue11,
      P.mainGrade=335 ∧ P.rescueGrade=319 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal9.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal9.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal9.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed11
end Z6969Source0811

-- Source: Research6969.PrefixMainDataHighQuadraticFinal10
section Z6969Source0812
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal10
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank23 1898, bank25 2129, bank32 2243, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank116 3644, bank168 4492, bank125 29117, bank150 6517, bank198 9780, bank183 54742, bank210 11036, bank174 148759, bank169 292467] i
  head := src1194
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![14908, 168210, 783398, 3876553],
    ![12303, 136754, 618235, 3055556],
    ![53398/9, 592714/9, 618235, 3055556],
    ![3599, 39922, 2895196/9, 14284348/9],
    ![60148/25, 693074/25, 210771, 4532641/4],
    ![16211/9, 183758/9, 1674843/8, 8440409/8],
    ![18775/16, 205865/16, 396682/3, 644809],
    ![89110/121, 957540/121, 4339504/49, 20734130/49],
    ![89110/121, 957540/121, 928879/12, 13482829/36],
    ![63754/121, 3201284/441, 543881/8, 13482829/36],
    ![63754/121, 777460/121, 4504528/75, 54849488/225],
    ![63754/121, 777460/121, 4504528/75, 25355094/121],
    ![675632/1681, 777460/121, 4504528/75, 25355094/121],
    ![675632/1681, 9519136/1681, 42853016/841, 25355094/121],
    ![675632/1681, 6967784/1323, 31341428/675, 25355094/121],
    ![954471/2738, 6967784/1323, 31341428/675, 25355094/121],
    ![954471/2738, 6970950/1369, 125491044/2809, 10969784/53],
    ![462882/1369, 6970950/1369, 125491044/2809, 10969784/53],
    ![459151/1369, 6970950/1369, 125491044/2809, 10969784/53]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 12 307995 := by
  refine ⟨?_, rank154 7526, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1194⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free23_0
    · exact free25_0
    · exact free32_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free116_1
    · exact free168_0
    · exact free125_0
    · exact free150_0
    · exact free198_0
    · exact free183_0
    · exact free210_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [346637688, 344269577, 345619771, 344389332, 346583922, 346431214, 345948067, 148276282, 148286168, 148015580, 115204231, 72174725, 70938634, 90577119, 104163548, 103997084, 126478123, 173508536, 234961833], [996477, 1002967, 999266, 1002639, 996624, 997043, 998367, 2595537, 2595373, 2599871, 3397567, 5553269, 5651510, 4386228, 3780627, 3786405, 3082416, 2189959, 1571839],
  ![124722440193060, 1605978237552, 211465649700, 4505821950], 189899439526341313⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6970950/1369, 125491044/2809, 10969784/53] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal10
end Z6969Source0812

-- Source: Research6969.PrefixNormalDataSeed12
section Z6969Source0813
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed12
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,12⟩
  bank i := ![bank245 91474, bank245 102908, bank245 115771, bank245 130242, bank245 146522, bank252 164837, bank270 164837, bank302 185441, bank303 208621, bank315 297039, bank347 297039] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307995
  seedFloor := 12

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 91474
    · exact rank245 102908
    · exact rank245 115771
    · exact rank245 130242
    · exact rank245 146522
    · exact rank252 164837
    · exact rank270 164837
    · exact rank302 185441
    · exact rank303 208621
    · exact rank315 297039
    · exact rank347 297039
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover508⟩
    · exact ⟨_, cover509⟩
    · exact ⟨_, cover510⟩
    · exact ⟨_, cover511⟩
    · exact ⟨_, cover512⟩
    · exact ⟨_, cover513⟩
    · exact ⟨_, cover514⟩
    · exact ⟨_, cover515⟩
    · exact ⟨_, cover516⟩
    · exact ⟨_, cover517⟩
    · exact ⟨_, cover518⟩

def price : NormalPrice := ⟨12, 95/100, 80/100, ![2479734653940, 221989487828, 8016323172, 668038800], 17507280825119066⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal10 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal10.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal10.price
    plan price SmallCertificates.primary12 SmallCertificates.rescue12 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 319
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 12))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 12 ≤ seedDegree G)
    (floor : 307995 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary12 SmallCertificates.rescue12) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal10.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal10.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal10.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 12))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 12 ≤ seedDegree G)
    (floor : 307995 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary12 SmallCertificates.rescue12,
      P.mainGrade=335 ∧ P.rescueGrade=319 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal10.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal10.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal10.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed12
end Z6969Source0813

-- Source: Research6969.PrefixMainDataHighQuadraticFinal11
section Z6969Source0814
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal11
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank120 36262, bank198 9780, bank210 11036, bank183 54742, bank174 148759, bank169 292467] i
  head := src1193
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 168947, 785812, 4106744],
    ![12303, 135854, 614185, 3014956],
    ![53398/9, 588814/9, 614185, 3014956],
    ![29433/8, 315889/8, 2859580/9, 13648988/9],
    ![16211/9, 20287, 1664093/8, 8328259/8],
    ![24292/27, 901708/81, 2048587/18, 11098157/18],
    ![73478/121, 106804/11, 5303810/49, 11098157/18],
    ![73478/121, 106804/11, 108095, 4607833/9],
    ![73478/121, 958366/121, 4296982/49, 18832336/49],
    ![63754/121, 3183884/441, 543881/8, 18832336/49],
    ![63754/121, 3183884/441, 543881/8, 43115356/121],
    ![61324/121, 3183884/441, 543881/8, 43115356/121],
    ![61324/121, 767012/121, 13252616/225, 55190032/225],
    ![61324/121, 767012/121, 13252616/225, 55190032/225],
    ![61324/121, 9451536/1681, 42551016/841, 193580968/841],
    ![667406/1681, 9451536/1681, 42551016/841, 193580968/841],
    ![667406/1681, 6919384/1323, 31125628/675, 9683504/45],
    ![667406/1681, 6921950/1369, 124616044/2809, 573673352/2809],
    ![954471/2738, 6921950/1369, 124616044/2809, 573673352/2809],
    ![462882/1369, 6921950/1369, 124616044/2809, 573673352/2809],
    ![459151/1369, 6921950/1369, 124616044/2809, 573673352/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 13 307921 := by
  refine ⟨?_, rank154 7426, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1193⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free210_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [343327582, 341189021, 341626312, 343212877, 341490189, 341440659, 342758902, 341873686, 166176893, 166760033, 166774755, 166775386, 82086581, 85399035, 66322186, 89606398, 103422350, 103280909, 125956610, 172987022, 234563942], [1005548, 1011409, 1010211, 1005863, 1010584, 1010720, 1007107, 1009533, 2297916, 2288221, 2287976, 2287965, 4858078, 4661386, 6057833, 4435179, 3810211, 3816181, 3096994, 2196248, 1575110],
  ![124511231692440, 1606407875728, 211107547800, 4541255390], 188682103096635776⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6921950/1369, 124616044/2809, 573673352/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal11
end Z6969Source0814

-- Source: Research6969.PhysicalChecks051
section Z6969Source0815
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src488 : Request := ⟨⟨⟨2100,2931,632,81311⟩,278060332482560,2021337557218⟩,1,2,1,307841,14⟩
private theorem pass488_2293 : (Triangular src488) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass488_2294 : (Triangular src488) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass488_2296 : (Triangular src488) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass488_2302 : (Triangular src488) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass488_2319 : (Triangular src488) 2319 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass488_2367 : (Triangular src488) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover488 : Cover (Triangular src488) 2389 2293 [2293,2295,2301,2318,2366,2389] := by
  exact ⟨by decide, by decide, pass488_2293, by decide, by decide, pass488_2294, by decide, by decide, pass488_2296, by decide, by decide, pass488_2302, by decide, by decide, pass488_2319, by decide, by decide, pass488_2367, rfl⟩
def src489 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,2,2,1,307841,14⟩
private theorem pass489_2293 : (Triangular src489) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass489_2298 : (Triangular src489) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass489_2312 : (Triangular src489) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass489_2352 : (Triangular src489) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover489 : Cover (Triangular src489) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass489_2293, by decide, by decide, pass489_2298, by decide, by decide, pass489_2312, by decide, by decide, pass489_2352, rfl⟩
def src490 : Request := ⟨⟨⟨1750,2442,518,115771⟩,158964379549696,962176592398⟩,3,2,1,307841,14⟩
private theorem pass490_2293 : (Triangular src490) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass490_2294 : (Triangular src490) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass490_2297 : (Triangular src490) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass490_2306 : (Triangular src490) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass490_2332 : (Triangular src490) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover490 : Cover (Triangular src490) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass490_2293, by decide, by decide, pass490_2294, by decide, by decide, pass490_2297, by decide, by decide, pass490_2306, by decide, by decide, pass490_2332, rfl⟩
def src491 : Request := ⟨⟨⟨2100,2930,622,102908⟩,274699477319680,1994139134137⟩,3,2,1,307841,14⟩
private theorem pass491_2293 : (Triangular src491) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass491_2294 : (Triangular src491) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass491_2297 : (Triangular src491) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass491_2306 : (Triangular src491) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass491_2332 : (Triangular src491) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover491 : Cover (Triangular src491) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass491_2293, by decide, by decide, pass491_2294, by decide, by decide, pass491_2297, by decide, by decide, pass491_2306, by decide, by decide, pass491_2332, rfl⟩
def src492 : Request := ⟨⟨⟨2600,3628,770,130242⟩,521059839508480,4684185417862⟩,6,2,1,307841,14⟩
private theorem pass492_2293 : (Triangular src492) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass492_2297 : (Triangular src492) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass492_2309 : (Triangular src492) 2309 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass492_2343 : (Triangular src492) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover492 : Cover (Triangular src492) 2389 2293 [2296,2308,2342,2389] := by
  exact ⟨by decide, by decide, pass492_2293, by decide, by decide, pass492_2297, by decide, by decide, pass492_2309, by decide, by decide, pass492_2343, rfl⟩
def src493 : Request := ⟨⟨⟨2600,3628,783,164837⟩,527755772952576,4745819470168⟩,10,2,1,307841,14⟩
private theorem pass493_2293 : (Triangular src493) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass493_2294 : (Triangular src493) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass493_2297 : (Triangular src493) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass493_2306 : (Triangular src493) 2306 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass493_2331 : (Triangular src493) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover493 : Cover (Triangular src493) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass493_2293, by decide, by decide, pass493_2294, by decide, by decide, pass493_2297, by decide, by decide, pass493_2306, by decide, by decide, pass493_2331, rfl⟩
def src494 : Request := ⟨⟨⟨3200,4465,963,146522⟩,983050615259136,10877088344236⟩,10,2,1,307841,14⟩
private theorem pass494_2293 : (Triangular src494) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass494_2295 : (Triangular src494) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass494_2300 : (Triangular src494) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass494_2314 : (Triangular src494) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass494_2354 : (Triangular src494) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover494 : Cover (Triangular src494) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass494_2293, by decide, by decide, pass494_2295, by decide, by decide, pass494_2300, by decide, by decide, pass494_2314, by decide, by decide, pass494_2354, rfl⟩
def src495 : Request := ⟨⟨⟨3950,5512,1189,164837⟩,1848744952463360,25255771038451⟩,13,2,1,307841,14⟩
private theorem pass495_2293 : (Triangular src495) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass495_2294 : (Triangular src495) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass495_2297 : (Triangular src495) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass495_2305 : (Triangular src495) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass495_2327 : (Triangular src495) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass495_2388 : (Triangular src495) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover495 : Cover (Triangular src495) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass495_2293, by decide, by decide, pass495_2294, by decide, by decide, pass495_2297, by decide, by decide, pass495_2305, by decide, by decide, pass495_2327, by decide, by decide, pass495_2388, rfl⟩
def src496 : Request := ⟨⟨⟨5700,7954,1716,264035⟩,5553838907981824,109473260530676⟩,25,2,1,307841,14⟩
private theorem pass496_2293 : (Triangular src496) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass496_2299 : (Triangular src496) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass496_2316 : (Triangular src496) 2316 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass496_2363 : (Triangular src496) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover496 : Cover (Triangular src496) 2389 2293 [2298,2315,2362,2389] := by
  exact ⟨by decide, by decide, pass496_2293, by decide, by decide, pass496_2299, by decide, by decide, pass496_2316, by decide, by decide, pass496_2363, rfl⟩
def src497 : Request := ⟨⟨⟨5700,7954,1716,334168⟩,5553838907981824,109473260530676⟩,32,2,1,307841,14⟩
private theorem pass497_2293 : (Triangular src497) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass497_2297 : (Triangular src497) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass497_2308 : (Triangular src497) 2308 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass497_2338 : (Triangular src497) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover497 : Cover (Triangular src497) 2389 2293 [2296,2307,2337,2389] := by
  exact ⟨by decide, by decide, pass497_2293, by decide, by decide, pass497_2297, by decide, by decide, pass497_2308, by decide, by decide, pass497_2338, rfl⟩
def src498 : Request := ⟨⟨⟨1750,2442,527,81311⟩,161065121873920,975196209190⟩,0,2,1,307921,13⟩
private theorem pass498_2293 : (Triangular src498) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass498_2295 : (Triangular src498) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass498_2300 : (Triangular src498) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass498_2315 : (Triangular src498) 2315 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass498_2357 : (Triangular src498) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover498 : Cover (Triangular src498) 2389 2293 [2294,2299,2314,2356,2389] := by
  exact ⟨by decide, by decide, pass498_2293, by decide, by decide, pass498_2295, by decide, by decide, pass498_2300, by decide, by decide, pass498_2315, by decide, by decide, pass498_2357, rfl⟩
def src499 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,1,2,1,307921,13⟩
private theorem pass499_2293 : (Triangular src499) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass499_2296 : (Triangular src499) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass499_2304 : (Triangular src499) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass499_2327 : (Triangular src499) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover499 : Cover (Triangular src499) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass499_2293, by decide, by decide, pass499_2296, by decide, by decide, pass499_2304, by decide, by decide, pass499_2327, rfl⟩
def src500 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,2,2,1,307921,13⟩
private theorem pass500_2293 : (Triangular src500) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass500_2295 : (Triangular src500) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass500_2301 : (Triangular src500) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass500_2318 : (Triangular src500) 2318 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass500_2367 : (Triangular src500) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover500 : Cover (Triangular src500) 2389 2293 [2294,2300,2317,2366,2389] := by
  exact ⟨by decide, by decide, pass500_2293, by decide, by decide, pass500_2295, by decide, by decide, pass500_2301, by decide, by decide, pass500_2318, by decide, by decide, pass500_2367, rfl⟩
def src501 : Request := ⟨⟨⟨2100,2930,632,115771⟩,278060332482560,2019119590628⟩,4,2,1,307921,13⟩
private theorem pass501_2293 : (Triangular src501) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass501_2295 : (Triangular src501) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass501_2300 : (Triangular src501) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass501_2314 : (Triangular src501) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass501_2354 : (Triangular src501) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover501 : Cover (Triangular src501) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass501_2293, by decide, by decide, pass501_2295, by decide, by decide, pass501_2300, by decide, by decide, pass501_2314, by decide, by decide, pass501_2354, rfl⟩
def src502 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,6,2,1,307921,13⟩
private theorem pass502_2293 : (Triangular src502) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass502_2295 : (Triangular src502) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass502_2301 : (Triangular src502) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass502_2318 : (Triangular src502) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass502_2366 : (Triangular src502) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover502 : Cover (Triangular src502) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass502_2293, by decide, by decide, pass502_2295, by decide, by decide, pass502_2301, by decide, by decide, pass502_2318, by decide, by decide, pass502_2366, rfl⟩
def src503 : Request := ⟨⟨⟨3200,4465,963,164837⟩,983050615259136,10877088344236⟩,10,2,1,307921,13⟩
private theorem pass503_2293 : (Triangular src503) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass503_2297 : (Triangular src503) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass503_2309 : (Triangular src503) 2309 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass503_2342 : (Triangular src503) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover503 : Cover (Triangular src503) 2389 2293 [2296,2308,2341,2389] := by
  exact ⟨by decide, by decide, pass503_2293, by decide, by decide, pass503_2297, by decide, by decide, pass503_2309, by decide, by decide, pass503_2342, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source0815

-- Source: Research6969.PrefixNormalDataSeed13
section Z6969Source0816
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed13
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,2,1,13⟩
  bank i := ![bank245 81311, bank245 91474, bank245 102908, bank252 115771, bank252 146522, bank303 164837, bank315 208621, bank270 264035, bank332 234698, bank314 422931] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307921
  seedFloor := 13

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 81311
    · exact rank245 91474
    · exact rank245 102908
    · exact rank252 115771
    · exact rank252 146522
    · exact rank303 164837
    · exact rank315 208621
    · exact rank270 264035
    · exact rank332 234698
    · exact rank314 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover498⟩
    · exact ⟨_, cover499⟩
    · exact ⟨_, cover500⟩
    · exact ⟨_, cover501⟩
    · exact ⟨_, cover502⟩
    · exact ⟨_, cover503⟩
    · exact ⟨_, cover505⟩
    · exact ⟨_, cover504⟩
    · exact ⟨_, cover506⟩
    · exact ⟨_, cover507⟩

def price : NormalPrice := ⟨13, 90/100, 80/100, ![2686379164200, 223267926040, 7312870450, 562538500], 15286339105750627⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal11 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal11.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal11.price
    plan price SmallCertificates.primary13 SmallCertificates.rescue13 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 256
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 13))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 13 ≤ seedDegree G)
    (floor : 307921 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary13 SmallCertificates.rescue13) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal11.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal11.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal11.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 13))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 13 ≤ seedDegree G)
    (floor : 307921 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary13 SmallCertificates.rescue13,
      P.mainGrade=335 ∧ P.rescueGrade=256 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal11.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal11.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal11.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed13
end Z6969Source0816

-- Source: Research6969.PrefixMainDataHighQuadraticFinal12
section Z6969Source0817
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal12
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 19
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 14, 13, 21, 18, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank44 2409, bank53 2871, bank62 3617, bank72 2841, bank84 5564, bank104 3359, bank137 3540, bank168 4492, bank125 29117, bank150 6517, bank198 9780, bank181 61748, bank212 10770, bank174 148759, bank169 292467] i
  head := src1192
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14876, 167196, 777376, 3825815],
    ![12303, 134954, 610135, 2974356],
    ![53398/9, 584914/9, 610135, 2974356],
    ![29433/8, 313739/8, 2840180/9, 1496132],
    ![16211/9, 181408/9, 1653343/8, 8216109/8],
    ![18775/16, 203115/16, 396682/3, 644809],
    ![86808/121, 86994/11, 4296996/49, 21032946/49],
    ![86808/121, 86994/11, 4296996/49, 21032946/49],
    ![86808/121, 86994/11, 4296996/49, 10406583/25],
    ![63754/121, 3166484/441, 543881/8, 20380932/49],
    ![63754/121, 3166484/441, 543881/8, 49216068/169],
    ![63754/121, 783924/121, 252225/4, 1152624/5],
    ![63754/121, 783924/121, 252225/4, 2243754/11],
    ![675632/1681, 783924/121, 252225/4, 2243754/11],
    ![675632/1681, 9383936/1681, 42249016/841, 2243754/11],
    ![675632/1681, 2290328/441, 10303276/225, 2243754/11],
    ![474397/1369, 2290328/441, 10303276/225, 2243754/11],
    ![474397/1369, 13767117/2738, 123585630/2809, 552307140/2809],
    ![462882/1369, 13767117/2738, 123585630/2809, 552307140/2809],
    ![459151/1369, 13767117/2738, 123585630/2809, 552307140/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 14 307841 := by
  refine ⟨?_, rank154 7326, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1192⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free44_0
    · exact free53_0
    · exact free62_0
    · exact free72_0
    · exact free84_0
    · exact free104_0
    · exact free137_0
    · exact free168_0
    · exact free125_0
    · exact free150_0
    · exact free198_0
    · exact free181_0
    · exact free212_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [341787488, 341116563, 341144819, 341682580, 340027131, 339521361, 147288481, 147223286, 147650649, 147775109, 147178201, 113894694, 73919046, 70300188, 89071748, 101196160, 101453735, 125093474, 172432324, 234141703], [1009769, 1011608, 1011530, 1010057, 1014594, 1015980, 2611960, 2613044, 2605939, 2603870, 2613794, 3442817, 5414635, 5702252, 4462139, 3904168, 3893297, 3121122, 2202937, 1578582],
  ![124287098786460, 1606864249892, 210727532700, 4645959920], 186679027578918589⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 13767117/2738, 123585630/2809, 552307140/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal12
end Z6969Source0817

-- Source: Research6969.PhysicalChecks050
section Z6969Source0818
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src472 : Request := ⟨⟨⟨3200,4465,947,130242⟩,970564165959680,10735676910569⟩,10,2,1,307664,16⟩
private theorem pass472_2293 : (Triangular src472) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass472_2294 : (Triangular src472) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass472_2297 : (Triangular src472) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass472_2305 : (Triangular src472) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass472_2328 : (Triangular src472) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover472 : Cover (Triangular src472) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass472_2293, by decide, by decide, pass472_2294, by decide, by decide, pass472_2297, by decide, by decide, pass472_2305, by decide, by decide, pass472_2328, rfl⟩
def src473 : Request := ⟨⟨⟨3200,4465,963,146522⟩,983050615259136,10877088344236⟩,13,2,1,307664,16⟩
private theorem pass473_2293 : (Triangular src473) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass473_2295 : (Triangular src473) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass473_2301 : (Triangular src473) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass473_2317 : (Triangular src473) 2317 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass473_2362 : (Triangular src473) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover473 : Cover (Triangular src473) 2389 2293 [2294,2300,2316,2361,2389] := by
  exact ⟨by decide, by decide, pass473_2293, by decide, by decide, pass473_2295, by decide, by decide, pass473_2301, by decide, by decide, pass473_2317, by decide, by decide, pass473_2362, rfl⟩
def src474 : Request := ⟨⟨⟨4800,6698,1445,185441⟩,3317023033262080,55058665830093⟩,20,2,1,307664,16⟩
private theorem pass474_2293 : (Triangular src474) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass474_2298 : (Triangular src474) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass474_2312 : (Triangular src474) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass474_2351 : (Triangular src474) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover474 : Cover (Triangular src474) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass474_2293, by decide, by decide, pass474_2298, by decide, by decide, pass474_2312, by decide, by decide, pass474_2351, rfl⟩
def src475 : Request := ⟨⟨⟨5700,7954,1716,264035⟩,5553838907981824,109473260530676⟩,32,2,1,307664,16⟩
private theorem pass475_2293 : (Triangular src475) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass475_2294 : (Triangular src475) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass475_2297 : (Triangular src475) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass475_2305 : (Triangular src475) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass475_2327 : (Triangular src475) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass475_2388 : (Triangular src475) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover475 : Cover (Triangular src475) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass475_2293, by decide, by decide, pass475_2294, by decide, by decide, pass475_2297, by decide, by decide, pass475_2305, by decide, by decide, pass475_2327, by decide, by decide, pass475_2388, rfl⟩
def src476 : Request := ⟨⟨⟨1450,2023,436,72277⟩,91566841790464,459151377566⟩,0,2,1,307755,15⟩
private theorem pass476_2293 : (Triangular src476) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass476_2295 : (Triangular src476) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass476_2301 : (Triangular src476) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass476_2318 : (Triangular src476) 2318 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass476_2367 : (Triangular src476) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover476 : Cover (Triangular src476) 2389 2293 [2294,2300,2317,2366,2389] := by
  exact ⟨by decide, by decide, pass476_2293, by decide, by decide, pass476_2295, by decide, by decide, pass476_2301, by decide, by decide, pass476_2318, by decide, by decide, pass476_2367, rfl⟩
def src477 : Request := ⟨⟨⟨1750,2442,518,81311⟩,158964379549696,962176592398⟩,1,2,1,307755,15⟩
private theorem pass477_2293 : (Triangular src477) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass477_2294 : (Triangular src477) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass477_2297 : (Triangular src477) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass477_2306 : (Triangular src477) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass477_2332 : (Triangular src477) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover477 : Cover (Triangular src477) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass477_2293, by decide, by decide, pass477_2294, by decide, by decide, pass477_2297, by decide, by decide, pass477_2306, by decide, by decide, pass477_2332, rfl⟩
def src478 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,3,2,1,307755,15⟩
private theorem pass478_2293 : (Triangular src478) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass478_2298 : (Triangular src478) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass478_2313 : (Triangular src478) 2313 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass478_2356 : (Triangular src478) 2356 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover478 : Cover (Triangular src478) 2389 2293 [2297,2312,2355,2389] := by
  exact ⟨by decide, by decide, pass478_2293, by decide, by decide, pass478_2298, by decide, by decide, pass478_2313, by decide, by decide, pass478_2356, rfl⟩
def src479 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,3,2,1,307755,15⟩
private theorem pass479_2293 : (Triangular src479) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass479_2298 : (Triangular src479) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass479_2312 : (Triangular src479) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass479_2352 : (Triangular src479) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover479 : Cover (Triangular src479) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass479_2293, by decide, by decide, pass479_2298, by decide, by decide, pass479_2312, by decide, by decide, pass479_2352, rfl⟩
def src480 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,4,2,1,307755,15⟩
private theorem pass480_2293 : (Triangular src480) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass480_2296 : (Triangular src480) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass480_2304 : (Triangular src480) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass480_2327 : (Triangular src480) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover480 : Cover (Triangular src480) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass480_2293, by decide, by decide, pass480_2296, by decide, by decide, pass480_2304, by decide, by decide, pass480_2327, rfl⟩
def src481 : Request := ⟨⟨⟨2100,2930,622,102908⟩,274699477319680,1994139134137⟩,4,2,1,307755,15⟩
private theorem pass481_2293 : (Triangular src481) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass481_2294 : (Triangular src481) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass481_2296 : (Triangular src481) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass481_2302 : (Triangular src481) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass481_2319 : (Triangular src481) 2319 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass481_2368 : (Triangular src481) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover481 : Cover (Triangular src481) 2389 2293 [2293,2295,2301,2318,2367,2389] := by
  exact ⟨by decide, by decide, pass481_2293, by decide, by decide, pass481_2294, by decide, by decide, pass481_2296, by decide, by decide, pass481_2302, by decide, by decide, pass481_2319, by decide, by decide, pass481_2368, rfl⟩
def src482 : Request := ⟨⟨⟨2600,3628,783,130242⟩,527755772952576,4745819470168⟩,8,2,1,307755,15⟩
private theorem pass482_2293 : (Triangular src482) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass482_2298 : (Triangular src482) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass482_2312 : (Triangular src482) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass482_2351 : (Triangular src482) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover482 : Cover (Triangular src482) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass482_2293, by decide, by decide, pass482_2298, by decide, by decide, pass482_2312, by decide, by decide, pass482_2351, rfl⟩
def src483 : Request := ⟨⟨⟨3200,4465,947,146522⟩,970564165959680,10735676910569⟩,10,2,1,307755,15⟩
private theorem pass483_2293 : (Triangular src483) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass483_2296 : (Triangular src483) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass483_2304 : (Triangular src483) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass483_2327 : (Triangular src483) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover483 : Cover (Triangular src483) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass483_2293, by decide, by decide, pass483_2296, by decide, by decide, pass483_2304, by decide, by decide, pass483_2327, rfl⟩
def src484 : Request := ⟨⟨⟨3200,4465,963,164837⟩,983050615259136,10877088344236⟩,13,2,1,307755,15⟩
private theorem pass484_2293 : (Triangular src484) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass484_2296 : (Triangular src484) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass484_2304 : (Triangular src484) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass484_2327 : (Triangular src484) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover484 : Cover (Triangular src484) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass484_2293, by decide, by decide, pass484_2296, by decide, by decide, pass484_2304, by decide, by decide, pass484_2327, rfl⟩
def src485 : Request := ⟨⟨⟨4800,6698,1445,208621⟩,3317023033262080,55058665830093⟩,20,2,1,307755,15⟩
private theorem pass485_2293 : (Triangular src485) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass485_2299 : (Triangular src485) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass485_2316 : (Triangular src485) 2316 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass485_2363 : (Triangular src485) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover485 : Cover (Triangular src485) 2389 2293 [2298,2315,2362,2389] := by
  exact ⟨by decide, by decide, pass485_2293, by decide, by decide, pass485_2299, by decide, by decide, pass485_2316, by decide, by decide, pass485_2363, rfl⟩
def src486 : Request := ⟨⟨⟨5700,7954,1716,297039⟩,5553838907981824,109473260530676⟩,32,2,1,307755,15⟩
private theorem pass486_2293 : (Triangular src486) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass486_2295 : (Triangular src486) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass486_2301 : (Triangular src486) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass486_2317 : (Triangular src486) 2317 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass486_2362 : (Triangular src486) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover486 : Cover (Triangular src486) 2389 2293 [2294,2300,2316,2361,2389] := by
  exact ⟨by decide, by decide, pass486_2293, by decide, by decide, pass486_2295, by decide, by decide, pass486_2301, by decide, by decide, pass486_2317, by decide, by decide, pass486_2362, rfl⟩
def src487 : Request := ⟨⟨⟨1450,2023,436,81311⟩,91566841790464,459151377566⟩,0,2,1,307841,14⟩
private theorem pass487_2293 : (Triangular src487) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass487_2297 : (Triangular src487) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass487_2308 : (Triangular src487) 2308 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass487_2340 : (Triangular src487) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover487 : Cover (Triangular src487) 2389 2293 [2296,2307,2339,2389] := by
  exact ⟨by decide, by decide, pass487_2293, by decide, by decide, pass487_2297, by decide, by decide, pass487_2308, by decide, by decide, pass487_2340, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source0818

-- Source: Research6969.PrefixNormalDataSeed14
section Z6969Source0819
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed14
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,14⟩
  bank i := ![bank236 81311, bank255 81311, bank252 91474, bank251 102908, bank244 115771, bank269 130242, bank303 146522, bank270 164837, bank315 164837, bank347 264035, bank347 334168] i
  reserve i := ![0, 1, 2, 3, 3, 6, 10, 10, 13, 25, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307841
  seedFloor := 14

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 81311
    · exact rank255 81311
    · exact rank252 91474
    · exact rank251 102908
    · exact rank244 115771
    · exact rank269 130242
    · exact rank303 146522
    · exact rank270 164837
    · exact rank315 164837
    · exact rank347 264035
    · exact rank347 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover487⟩
    · exact ⟨_, cover488⟩
    · exact ⟨_, cover489⟩
    · exact ⟨_, cover491⟩
    · exact ⟨_, cover490⟩
    · exact ⟨_, cover492⟩
    · exact ⟨_, cover494⟩
    · exact ⟨_, cover493⟩
    · exact ⟨_, cover495⟩
    · exact ⟨_, cover496⟩
    · exact ⟨_, cover497⟩

def price : NormalPrice := ⟨14, 90/100, 80/100, ![2893023674460, 224546364252, 9352376748, 668038800], 14867945835023022⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal12 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal12.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal12.price
    plan price SmallCertificates.primary14 SmallCertificates.rescue14 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 293
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 14))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 14 ≤ seedDegree G)
    (floor : 307841 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary14 SmallCertificates.rescue14) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal12.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal12.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal12.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 14))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 14 ≤ seedDegree G)
    (floor : 307841 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary14 SmallCertificates.rescue14,
      P.mainGrade=335 ∧ P.rescueGrade=293 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal12.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal12.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal12.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed14
end Z6969Source0819

-- Source: Research6969.PrefixMainDataHighQuadraticFinal13
section Z6969Source0820
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal13
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank121 32187, bank198 9780, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1191
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 168353, 782644, 4076450],
    ![12303, 134072, 606166, 2934568],
    ![53398/9, 581092/9, 606166, 2934568],
    ![29433/8, 38954, 2821168/9, 13285064/9],
    ![16211/9, 40057/2, 205351, 4053101/4],
    ![24292/27, 891214/81, 1012364/9, 5401123/9],
    ![73478/121, 105832/11, 5256092/49, 5401123/9],
    ![73478/121, 105832/11, 106632, 4484974/9],
    ![73478/121, 944308/121, 4234612/49, 18330208/49],
    ![63754/121, 3149432/441, 543881/8, 18330208/49],
    ![63754/121, 3149432/441, 543881/8, 41965768/121],
    ![61324/121, 3149432/441, 543881/8, 41965768/121],
    ![61324/121, 755726/121, 235037/4, 53718496/225],
    ![61324/121, 755726/121, 235037/4, 53718496/225],
    ![61324/121, 9317688/1681, 100415/2, 188419504/841],
    ![671521/1681, 9317688/1681, 100415/2, 188419504/841],
    ![671521/1681, 6823552/1323, 30698344/675, 9425312/45],
    ![671521/1681, 6834338/1369, 219708/5, 544918920/2809],
    ![954471/2738, 6834338/1369, 219708/5, 544918920/2809],
    ![462882/1369, 6834338/1369, 219708/5, 544918920/2809],
    ![459151/1369, 6834338/1369, 219708/5, 544918920/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 15 307755 := by
  refine ⟨?_, rank154 7228, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1191⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free150_0
    · exact free121_0
    · exact free198_0
    · exact free212_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [339550930, 339238879, 338727720, 339254986, 337514555, 338518759, 338852278, 339179408, 168294376, 168699440, 168586567, 168329140, 81353571, 84522780, 72515807, 90245608, 104272541, 104306061, 125185301, 172215713, 233974394], [1015899, 1016754, 1018155, 1016710, 1021480, 1018727, 1017813, 1016917, 2262710, 2255976, 2257852, 2262132, 4901604, 4713418, 5526160, 4402945, 3776843, 3775679, 3118555, 2205549, 1579957],
  ![124198287823080, 1607044684636, 210576954600, 4494443170], 186320372405965399⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6834338/1369, 219708/5, 544918920/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal13
end Z6969Source0820

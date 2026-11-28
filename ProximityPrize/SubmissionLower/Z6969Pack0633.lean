import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 11 308048 := by
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

def price : Pricing := ⟨55/100, 90/100, [347237618, 345737371, 346866748, 345292806, 345345864, 346411895, 345454338, 346601321, 167393660, 167913672, 168100202, 167868382, 115705130, 74375446, 67007639, 91113394, 105978186, 105482226, 127004852, 174035264, 235363704], [995052, 999164, 996068, 1000383, 1000238, 997315, 999940, 996796, 2278188, 2269540, 2266438, 2270293, 3384311, 5379547, 5997038, 4360146, 3718453, 3735673, 3068368, 2184089, 1568881],
  ![124935761357280, 1605544152636, 211827333600, 4446368700], 191210590053437783⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,9,15,16,12,10,10,9,6,5] (by decide +kernel) i⟩
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
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src504 : Request := ⟨⟨⟨2600,3628,783,264035⟩,527755772952576,4745819470168⟩,13,2,1,307912,13⟩
theorem cover504 : PhysicalWindow.Cover (PhysicalWindow.Triangular src504) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src505 : Request := ⟨⟨⟨3950,5512,1189,208621⟩,1848744952463360,25255771038451⟩,16,2,1,307912,13⟩
theorem cover505 : PhysicalWindow.Cover (PhysicalWindow.Triangular src505) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src506 : Request := ⟨⟨⟨4800,6698,1445,234698⟩,3317023033262080,55058665830093⟩,20,2,1,307912,13⟩
theorem cover506 : PhysicalWindow.Cover (PhysicalWindow.Triangular src506) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src507 : Request := ⟨⟨⟨3950,5512,1169,422931⟩,1824966114017280,24923274283249⟩,25,2,1,307912,13⟩
theorem cover507 : PhysicalWindow.Cover (PhysicalWindow.Triangular src507) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src508 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,0,2,1,307983,12⟩
theorem cover508 : PhysicalWindow.Cover (PhysicalWindow.Triangular src508) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
def src509 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,1,2,1,307983,12⟩
theorem cover509 : PhysicalWindow.Cover (PhysicalWindow.Triangular src509) 2411 2314 [2321, 2344, 2409, 2411] := triangleCover (by decide +kernel)
def src510 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,2,2,1,307983,12⟩
theorem cover510 : PhysicalWindow.Cover (PhysicalWindow.Triangular src510) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
def src511 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,3,2,1,307983,12⟩
theorem cover511 : PhysicalWindow.Cover (PhysicalWindow.Triangular src511) 2411 2314 [2318, 2333, 2375, 2411] := triangleCover (by decide +kernel)
def src512 : Request := ⟨⟨⟨1750,2442,527,146522⟩,161065121873920,975196209190⟩,4,2,1,307983,12⟩
theorem cover512 : PhysicalWindow.Cover (PhysicalWindow.Triangular src512) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src513 : Request := ⟨⟨⟨2100,2930,632,164837⟩,278060332482560,2019119590628⟩,6,2,1,307983,12⟩
theorem cover513 : PhysicalWindow.Cover (PhysicalWindow.Triangular src513) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src514 : Request := ⟨⟨⟨2600,3628,783,164837⟩,527755772952576,4745819470168⟩,8,2,1,307983,12⟩
theorem cover514 : PhysicalWindow.Cover (PhysicalWindow.Triangular src514) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src515 : Request := ⟨⟨⟨3200,4465,947,185441⟩,970564165959680,10735676910569⟩,10,2,1,307983,12⟩
theorem cover515 : PhysicalWindow.Cover (PhysicalWindow.Triangular src515) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src516 : Request := ⟨⟨⟨3200,4465,963,208621⟩,983050615259136,10877088344236⟩,13,2,1,307983,12⟩
theorem cover516 : PhysicalWindow.Cover (PhysicalWindow.Triangular src516) 2411 2314 [2316, 2324, 2346, 2408, 2411] := triangleCover (by decide +kernel)
def src517 : Request := ⟨⟨⟨3950,5512,1189,297039⟩,1848744952463360,25255771038451⟩,20,2,1,307983,12⟩
theorem cover517 : PhysicalWindow.Cover (PhysicalWindow.Triangular src517) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src518 : Request := ⟨⟨⟨5700,7954,1716,297039⟩,5553838907981824,109473260530676⟩,25,2,1,307983,12⟩
theorem cover518 : PhysicalWindow.Cover (PhysicalWindow.Triangular src518) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src519 : Request := ⟨⟨⟨1450,2023,436,102908⟩,91566841790464,459151377566⟩,0,2,1,308048,11⟩
theorem cover519 : PhysicalWindow.Cover (PhysicalWindow.Triangular src519) 2411 2314 [2318, 2332, 2373, 2411] := triangleCover (by decide +kernel)
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
  physicalFloor := 308048
  seedFloor := 11

theorem sources : plan.Sources 2314 2411 := by
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

def price : NormalPrice := ⟨11, 95/100, 80/100, ![2273090674500, 220711052900, 7348298100, 668038800], 19513314941434316⟩
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
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 11))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 11 ≤ seedDegree G)
    (floor : 308048 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary11 SmallCertificates.rescue11) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal9.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal9.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal9.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 11))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 11 ≤ seedDegree G)
    (floor : 308048 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 12 307983 := by
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

def price : Pricing := ⟨55/100, 90/100, [346637688, 344269577, 345619771, 344389332, 346583922, 346431214, 345948067, 148276282, 148286168, 148015580, 115204231, 72174725, 70938634, 90577119, 104163548, 103997084, 126478123, 173508536, 234961833], [996696, 1003188, 999487, 1002860, 996844, 997262, 998587, 2596109, 2595945, 2600445, 3398316, 5554493, 5652756, 4387195, 3781460, 3787240, 3083095, 2190442, 1572185],
  ![124722440193060, 1605978237552, 211465649700, 4505821950], 189920062983760142⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,7,7,7,9,15,15,12,10,10,9,6,5] (by decide +kernel) i⟩
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
  physicalFloor := 307983
  seedFloor := 12

theorem sources : plan.Sources 2314 2411 := by
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

def price : NormalPrice := ⟨12, 95/100, 80/100, ![2479734653940, 221989487828, 8016323172, 668038800], 17511042678032626⟩
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
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 12))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 12 ≤ seedDegree G)
    (floor : 307983 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary12 SmallCertificates.rescue12) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal10.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal10.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal10.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 12))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 12 ≤ seedDegree G)
    (floor : 307983 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 13 307912 := by
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

def price : Pricing := ⟨55/100, 90/100, [343327582, 341189021, 341626312, 343212877, 341490189, 341440659, 342758902, 341873686, 166176893, 166760033, 166774755, 166775386, 82086581, 85399035, 66322186, 89606398, 103422350, 103280909, 125956610, 172987022, 234563942], [1005770, 1011632, 1010434, 1006084, 1010807, 1010942, 1007329, 1009755, 2298423, 2288725, 2288480, 2288470, 4859149, 4662414, 6059169, 4436157, 3811051, 3817022, 3097677, 2196732, 1575458],
  ![124511231692440, 1606407875728, 211107547800, 4541255390], 188702832136578163⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,13,13,16,12,11,11,9,6,5] (by decide +kernel) i⟩
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
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src488 : Request := ⟨⟨⟨2100,2931,632,81311⟩,278060332482560,2021337557218⟩,1,2,1,307836,14⟩
theorem cover488 : PhysicalWindow.Cover (PhysicalWindow.Triangular src488) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src489 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,2,2,1,307836,14⟩
theorem cover489 : PhysicalWindow.Cover (PhysicalWindow.Triangular src489) 2411 2314 [2320, 2339, 2393, 2411] := triangleCover (by decide +kernel)
def src490 : Request := ⟨⟨⟨1750,2442,518,115771⟩,158964379549696,962176592398⟩,3,2,1,307836,14⟩
theorem cover490 : PhysicalWindow.Cover (PhysicalWindow.Triangular src490) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src491 : Request := ⟨⟨⟨2100,2930,622,102908⟩,274699477319680,1994139134137⟩,3,2,1,307836,14⟩
theorem cover491 : PhysicalWindow.Cover (PhysicalWindow.Triangular src491) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src492 : Request := ⟨⟨⟨2600,3628,770,130242⟩,521059839508480,4684185417862⟩,6,2,1,307836,14⟩
theorem cover492 : PhysicalWindow.Cover (PhysicalWindow.Triangular src492) 2411 2314 [2319, 2337, 2388, 2411] := triangleCover (by decide +kernel)
def src493 : Request := ⟨⟨⟨2600,3628,783,164837⟩,527755772952576,4745819470168⟩,10,2,1,307836,14⟩
theorem cover493 : PhysicalWindow.Cover (PhysicalWindow.Triangular src493) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src494 : Request := ⟨⟨⟨3200,4465,963,146522⟩,983050615259136,10877088344236⟩,10,2,1,307836,14⟩
theorem cover494 : PhysicalWindow.Cover (PhysicalWindow.Triangular src494) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src495 : Request := ⟨⟨⟨3950,5512,1189,164837⟩,1848744952463360,25255771038451⟩,13,2,1,307836,14⟩
theorem cover495 : PhysicalWindow.Cover (PhysicalWindow.Triangular src495) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src496 : Request := ⟨⟨⟨5700,7954,1716,264035⟩,5553838907981824,109473260530676⟩,25,2,1,307836,14⟩
theorem cover496 : PhysicalWindow.Cover (PhysicalWindow.Triangular src496) 2411 2314 [2320, 2340, 2395, 2411] := triangleCover (by decide +kernel)
def src497 : Request := ⟨⟨⟨5700,7954,1716,334168⟩,5553838907981824,109473260530676⟩,32,2,1,307836,14⟩
theorem cover497 : PhysicalWindow.Cover (PhysicalWindow.Triangular src497) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src498 : Request := ⟨⟨⟨1750,2442,527,81311⟩,161065121873920,975196209190⟩,0,2,1,307912,13⟩
theorem cover498 : PhysicalWindow.Cover (PhysicalWindow.Triangular src498) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src499 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,1,2,1,307912,13⟩
theorem cover499 : PhysicalWindow.Cover (PhysicalWindow.Triangular src499) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src500 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,2,2,1,307912,13⟩
theorem cover500 : PhysicalWindow.Cover (PhysicalWindow.Triangular src500) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src501 : Request := ⟨⟨⟨2100,2930,632,115771⟩,278060332482560,2019119590628⟩,4,2,1,307912,13⟩
theorem cover501 : PhysicalWindow.Cover (PhysicalWindow.Triangular src501) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src502 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,6,2,1,307912,13⟩
theorem cover502 : PhysicalWindow.Cover (PhysicalWindow.Triangular src502) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src503 : Request := ⟨⟨⟨3200,4465,963,164837⟩,983050615259136,10877088344236⟩,10,2,1,307912,13⟩
theorem cover503 : PhysicalWindow.Cover (PhysicalWindow.Triangular src503) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
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
  physicalFloor := 307912
  seedFloor := 13

theorem sources : plan.Sources 2314 2411 := by
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

def price : NormalPrice := ⟨13, 90/100, 80/100, ![2686379164200, 223267926040, 7312870450, 562538500], 15289619798520233⟩
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
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 13))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 13 ≤ seedDegree G)
    (floor : 307912 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary13 SmallCertificates.rescue13) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal11.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal11.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal11.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 13))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 13 ≤ seedDegree G)
    (floor : 307912 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 14 307836 := by
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

def price : Pricing := ⟨55/100, 90/100, [341787488, 341116563, 341144819, 341682580, 340027131, 339521361, 147288481, 147223286, 147650649, 147775109, 147178201, 113894694, 73919046, 70300188, 89071748, 101196160, 101453735, 125093474, 172432324, 234141703], [1009992, 1011831, 1011753, 1010279, 1014817, 1016204, 2612536, 2613621, 2606513, 2604444, 2614370, 3443577, 5415829, 5703509, 4463123, 3905029, 3894155, 3121810, 2203422, 1578930],
  ![124287098786460, 1606864249892, 210727532700, 4645959920], 186699331201095497⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,7,7,7,7,7,10,15,15,12,11,11,9,6,5] (by decide +kernel) i⟩
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
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src472 : Request := ⟨⟨⟨3200,4465,947,130242⟩,970564165959680,10735676910569⟩,10,2,1,307664,16⟩
theorem cover472 : PhysicalWindow.Cover (PhysicalWindow.Triangular src472) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src473 : Request := ⟨⟨⟨3200,4465,963,146522⟩,983050615259136,10877088344236⟩,13,2,1,307664,16⟩
theorem cover473 : PhysicalWindow.Cover (PhysicalWindow.Triangular src473) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src474 : Request := ⟨⟨⟨4800,6698,1445,185441⟩,3317023033262080,55058665830093⟩,20,2,1,307664,16⟩
theorem cover474 : PhysicalWindow.Cover (PhysicalWindow.Triangular src474) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src475 : Request := ⟨⟨⟨5700,7954,1716,264035⟩,5553838907981824,109473260530676⟩,32,2,1,307664,16⟩
theorem cover475 : PhysicalWindow.Cover (PhysicalWindow.Triangular src475) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src476 : Request := ⟨⟨⟨1450,2023,436,72277⟩,91566841790464,459151377566⟩,0,2,1,307754,15⟩
theorem cover476 : PhysicalWindow.Cover (PhysicalWindow.Triangular src476) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src477 : Request := ⟨⟨⟨1750,2442,518,81311⟩,158964379549696,962176592398⟩,1,2,1,307754,15⟩
theorem cover477 : PhysicalWindow.Cover (PhysicalWindow.Triangular src477) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src478 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,3,2,1,307754,15⟩
theorem cover478 : PhysicalWindow.Cover (PhysicalWindow.Triangular src478) 2411 2314 [2320, 2341, 2401, 2411] := triangleCover (by decide +kernel)
def src479 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,3,2,1,307754,15⟩
theorem cover479 : PhysicalWindow.Cover (PhysicalWindow.Triangular src479) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
def src480 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,4,2,1,307754,15⟩
theorem cover480 : PhysicalWindow.Cover (PhysicalWindow.Triangular src480) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src481 : Request := ⟨⟨⟨2100,2930,622,102908⟩,274699477319680,1994139134137⟩,4,2,1,307754,15⟩
theorem cover481 : PhysicalWindow.Cover (PhysicalWindow.Triangular src481) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src482 : Request := ⟨⟨⟨2600,3628,783,130242⟩,527755772952576,4745819470168⟩,8,2,1,307754,15⟩
theorem cover482 : PhysicalWindow.Cover (PhysicalWindow.Triangular src482) 2411 2314 [2320, 2339, 2393, 2411] := triangleCover (by decide +kernel)
def src483 : Request := ⟨⟨⟨3200,4465,947,146522⟩,970564165959680,10735676910569⟩,10,2,1,307754,15⟩
theorem cover483 : PhysicalWindow.Cover (PhysicalWindow.Triangular src483) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src484 : Request := ⟨⟨⟨3200,4465,963,164837⟩,983050615259136,10877088344236⟩,13,2,1,307754,15⟩
theorem cover484 : PhysicalWindow.Cover (PhysicalWindow.Triangular src484) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src485 : Request := ⟨⟨⟨4800,6698,1445,208621⟩,3317023033262080,55058665830093⟩,20,2,1,307754,15⟩
theorem cover485 : PhysicalWindow.Cover (PhysicalWindow.Triangular src485) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src486 : Request := ⟨⟨⟨5700,7954,1716,297039⟩,5553838907981824,109473260530676⟩,32,2,1,307754,15⟩
theorem cover486 : PhysicalWindow.Cover (PhysicalWindow.Triangular src486) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src487 : Request := ⟨⟨⟨1450,2023,436,81311⟩,91566841790464,459151377566⟩,0,2,1,307836,14⟩
theorem cover487 : PhysicalWindow.Cover (PhysicalWindow.Triangular src487) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
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
  physicalFloor := 307836
  seedFloor := 14

theorem sources : plan.Sources 2314 2411 := by
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

def price : NormalPrice := ⟨14, 90/100, 80/100, ![2893023674460, 224546364252, 9352376748, 668038800], 14871135711312628⟩
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
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 14))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 14 ≤ seedDegree G)
    (floor : 307836 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary14 SmallCertificates.rescue14) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal12.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal12.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal12.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 14))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 14 ≤ seedDegree G)
    (floor : 307836 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 15 307754 := by
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

def price : Pricing := ⟨55/100, 90/100, [339550930, 339238879, 338727720, 339254986, 337514555, 338518759, 338852278, 339179408, 168294376, 168699440, 168586567, 168329140, 81353571, 84522780, 72515807, 90245608, 104272541, 104306061, 125185301, 172215713, 233974394], [1016123, 1016978, 1018379, 1016934, 1021705, 1018952, 1018038, 1017141, 2263209, 2256473, 2258350, 2262631, 4902685, 4714457, 5527379, 4403916, 3777676, 3776512, 3119243, 2206035, 1580306],
  ![124198287823080, 1607044684636, 210576954600, 4494443170], 186340940017700043⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,13,13,15,12,10,10,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6834338/1369, 219708/5, 544918920/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal13
end Z6969Source0820

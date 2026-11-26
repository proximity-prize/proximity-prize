import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0633
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0589
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Z6969Pack0520
import ProximityPrize.SubmissionLower.Z6969Pack0427
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- Source: Research6969.PrefixNormalDataSeed15
section Z6969Source0821
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed15
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,15⟩
  bank i := ![bank236 72277, bank244 81311, bank252 91474, bank245 102908, bank251 102908, bank245 115771, bank270 130242, bank302 146522, bank303 164837, bank332 208621, bank347 297039] i
  reserve i := ![0, 1, 3, 3, 4, 4, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307755
  seedFloor := 15

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 72277
    · exact rank244 81311
    · exact rank252 91474
    · exact rank245 102908
    · exact rank251 102908
    · exact rank245 115771
    · exact rank270 130242
    · exact rank302 146522
    · exact rank303 164837
    · exact rank332 208621
    · exact rank347 297039
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover476⟩
    · exact ⟨_, cover477⟩
    · exact ⟨_, cover479⟩
    · exact ⟨_, cover478⟩
    · exact ⟨_, cover481⟩
    · exact ⟨_, cover480⟩
    · exact ⟨_, cover482⟩
    · exact ⟨_, cover483⟩
    · exact ⟨_, cover484⟩
    · exact ⟨_, cover485⟩
    · exact ⟨_, cover486⟩

def price : NormalPrice := ⟨15, 90/100, 80/100, ![3099668184720, 225824802464, 10020403536, 668038800], 13112079970355718⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal13 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal13.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal13.price
    plan price SmallCertificates.primary15 SmallCertificates.rescue15 where
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
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 15))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 15 ≤ seedDegree G)
    (floor : 307755 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary15 SmallCertificates.rescue15) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal13.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal13.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal13.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 15))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 15 ≤ seedDegree G)
    (floor : 307755 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary15 SmallCertificates.rescue15,
      P.mainGrade=335 ∧ P.rescueGrade=293 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal13.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal13.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal13.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed15
end Z6969Source0821

-- Source: Research6969.PrefixMainDataHighQuadraticFinal14
section Z6969Source0822
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal14
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank121 32187, bank198 9780, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1190
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 168062, 781092, 4061609],
    ![12303, 133199, 1204475/2, 2895186],
    ![53398/9, 577309/9, 1204475/2, 2895186],
    ![29433/8, 619093/16, 2802350/9, 4368926/3],
    ![16211/9, 716467/36, 3264761/16, 15994833/16],
    ![24292/27, 886073/81, 4026079/36, 7104853/12],
    ![73478/121, 1158914/121, 5232715/49, 7104853/12],
    ![73478/121, 1158914/121, 1906475/18, 2949857/6],
    ![73478/121, 937421/121, 4204057/49, 18084216/49],
    ![63754/121, 3132554/441, 543881/8, 18084216/49],
    ![63754/121, 3132554/441, 543881/8, 41402586/121],
    ![61324/121, 3132554/441, 543881/8, 41402586/121],
    ![61324/121, 750197/121, 235037/4, 17665864/75],
    ![61324/121, 750197/121, 235037/4, 17665864/75],
    ![61324/121, 9252116/1681, 100415/2, 185890908/841],
    ![671521/1681, 9252116/1681, 100415/2, 185890908/841],
    ![671521/1681, 752956/147, 10163006/225, 3099608/15],
    ![671521/1681, 27142479/5476, 219708/5, 537606090/2809],
    ![954471/2738, 27142479/5476, 219708/5, 537606090/2809],
    ![462882/1369, 27142479/5476, 219708/5, 537606090/2809],
    ![459151/1369, 27142479/5476, 219708/5, 537606090/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 16 307664 := by
  refine ⟨?_, rank154 7131, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1190⟩⟩
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

def price : Pricing := ⟨55/100, 90/100, [337700752, 337181060, 336004369, 336741499, 336916566, 336411906, 336906862, 335970315, 166673743, 166697715, 167188636, 167139984, 70496896, 83794317, 72423544, 88183894, 102348147, 102432460, 125035338, 172065750, 233857527], [1020969, 1022393, 1025618, 1023598, 1023118, 1024501, 1023145, 1025712, 2289655, 2289257, 2281095, 2281904, 5686618, 4756673, 5533493, 4506911, 3855548, 3851990, 3122747, 2207357, 1580918],
  ![124136252482140, 1607171011428, 210471774300, 4597049220], 185228290944896622⟩

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
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 27142479/5476, 219708/5, 537606090/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal14
end Z6969Source0822

-- Source: Research6969.PhysicalChecks049
section Z6969Source0823
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src456 : Request := ⟨⟨⟨1750,2442,527,72277⟩,161065121873920,975196209190⟩,2,2,1,307566,17⟩
private theorem pass456_2293 : (Triangular src456) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass456_2299 : (Triangular src456) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass456_2316 : (Triangular src456) 2316 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass456_2365 : (Triangular src456) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover456 : Cover (Triangular src456) 2389 2293 [2298,2315,2364,2389] := by
  exact ⟨by decide, by decide, pass456_2293, by decide, by decide, pass456_2299, by decide, by decide, pass456_2316, by decide, by decide, pass456_2365, rfl⟩
def src457 : Request := ⟨⟨⟨1750,2442,527,81311⟩,161065121873920,975196209190⟩,3,2,1,307566,17⟩
private theorem pass457_2293 : (Triangular src457) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass457_2298 : (Triangular src457) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass457_2312 : (Triangular src457) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass457_2352 : (Triangular src457) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover457 : Cover (Triangular src457) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass457_2293, by decide, by decide, pass457_2298, by decide, by decide, pass457_2312, by decide, by decide, pass457_2352, rfl⟩
def src458 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,4,2,1,307566,17⟩
private theorem pass458_2293 : (Triangular src458) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass458_2295 : (Triangular src458) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass458_2301 : (Triangular src458) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass458_2318 : (Triangular src458) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass458_2366 : (Triangular src458) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover458 : Cover (Triangular src458) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass458_2293, by decide, by decide, pass458_2295, by decide, by decide, pass458_2301, by decide, by decide, pass458_2318, by decide, by decide, pass458_2366, rfl⟩
def src459 : Request := ⟨⟨⟨2100,2930,632,102908⟩,278060332482560,2019119590628⟩,6,2,1,307566,17⟩
private theorem pass459_2293 : (Triangular src459) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass459_2299 : (Triangular src459) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass459_2316 : (Triangular src459) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass459_2364 : (Triangular src459) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover459 : Cover (Triangular src459) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass459_2293, by decide, by decide, pass459_2299, by decide, by decide, pass459_2316, by decide, by decide, pass459_2364, rfl⟩
def src460 : Request := ⟨⟨⟨2600,3628,783,102908⟩,527755772952576,4745819470168⟩,8,2,1,307566,17⟩
private theorem pass460_2293 : (Triangular src460) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass460_2296 : (Triangular src460) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass460_2305 : (Triangular src460) 2305 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass460_2330 : (Triangular src460) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover460 : Cover (Triangular src460) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass460_2293, by decide, by decide, pass460_2296, by decide, by decide, pass460_2305, by decide, by decide, pass460_2330, rfl⟩
def src461 : Request := ⟨⟨⟨3200,4465,963,115771⟩,983050615259136,10877088344236⟩,10,2,1,307566,17⟩
private theorem pass461_2293 : (Triangular src461) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass461_2301 : (Triangular src461) 2301 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass461_2323 : (Triangular src461) 2323 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass461_2385 : (Triangular src461) 2385 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover461 : Cover (Triangular src461) 2389 2293 [2300,2322,2384,2389] := by
  exact ⟨by decide, by decide, pass461_2293, by decide, by decide, pass461_2301, by decide, by decide, pass461_2323, by decide, by decide, pass461_2385, rfl⟩
def src462 : Request := ⟨⟨⟨3200,4465,963,130242⟩,983050615259136,10877088344236⟩,13,2,1,307566,17⟩
private theorem pass462_2293 : (Triangular src462) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass462_2295 : (Triangular src462) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass462_2300 : (Triangular src462) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass462_2314 : (Triangular src462) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass462_2354 : (Triangular src462) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover462 : Cover (Triangular src462) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass462_2293, by decide, by decide, pass462_2295, by decide, by decide, pass462_2300, by decide, by decide, pass462_2314, by decide, by decide, pass462_2354, rfl⟩
def src463 : Request := ⟨⟨⟨4800,6698,1445,164837⟩,3317023033262080,55058665830093⟩,20,2,1,307566,17⟩
private theorem pass463_2293 : (Triangular src463) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass463_2297 : (Triangular src463) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass463_2308 : (Triangular src463) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass463_2339 : (Triangular src463) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover463 : Cover (Triangular src463) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass463_2293, by decide, by decide, pass463_2297, by decide, by decide, pass463_2308, by decide, by decide, pass463_2339, rfl⟩
def src464 : Request := ⟨⟨⟨5700,7954,1716,234698⟩,5553838907981824,109473260530676⟩,32,2,1,307566,17⟩
private theorem pass464_2293 : (Triangular src464) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass464_2294 : (Triangular src464) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass464_2297 : (Triangular src464) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass464_2305 : (Triangular src464) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass464_2327 : (Triangular src464) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass464_2388 : (Triangular src464) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover464 : Cover (Triangular src464) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass464_2293, by decide, by decide, pass464_2294, by decide, by decide, pass464_2297, by decide, by decide, pass464_2305, by decide, by decide, pass464_2327, by decide, by decide, pass464_2388, rfl⟩
def src465 : Request := ⟨⟨⟨1450,2023,436,64247⟩,91566841790464,459151377566⟩,0,2,1,307664,16⟩
private theorem pass465_2293 : (Triangular src465) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass465_2294 : (Triangular src465) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass465_2297 : (Triangular src465) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass465_2305 : (Triangular src465) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass465_2328 : (Triangular src465) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover465 : Cover (Triangular src465) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass465_2293, by decide, by decide, pass465_2294, by decide, by decide, pass465_2297, by decide, by decide, pass465_2305, by decide, by decide, pass465_2328, rfl⟩
def src466 : Request := ⟨⟨⟨1750,2442,527,72277⟩,161065121873920,975196209190⟩,1,2,1,307664,16⟩
private theorem pass466_2293 : (Triangular src466) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass466_2300 : (Triangular src466) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass466_2320 : (Triangular src466) 2320 2376 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass466_2377 : (Triangular src466) 2377 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover466 : Cover (Triangular src466) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass466_2293, by decide, by decide, pass466_2300, by decide, by decide, pass466_2320, by decide, by decide, pass466_2377, rfl⟩
def src467 : Request := ⟨⟨⟨2100,2930,632,72277⟩,278060332482560,2019119590628⟩,2,2,1,307664,16⟩
private theorem pass467_2293 : (Triangular src467) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass467_2294 : (Triangular src467) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass467_2296 : (Triangular src467) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass467_2302 : (Triangular src467) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass467_2319 : (Triangular src467) 2319 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass467_2367 : (Triangular src467) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover467 : Cover (Triangular src467) 2389 2293 [2293,2295,2301,2318,2366,2389] := by
  exact ⟨by decide, by decide, pass467_2293, by decide, by decide, pass467_2294, by decide, by decide, pass467_2296, by decide, by decide, pass467_2302, by decide, by decide, pass467_2319, by decide, by decide, pass467_2367, rfl⟩
def src468 : Request := ⟨⟨⟨2100,2930,632,81311⟩,278060332482560,2019119590628⟩,3,2,1,307664,16⟩
private theorem pass468_2293 : (Triangular src468) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass468_2297 : (Triangular src468) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass468_2308 : (Triangular src468) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass468_2339 : (Triangular src468) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover468 : Cover (Triangular src468) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass468_2293, by decide, by decide, pass468_2297, by decide, by decide, pass468_2308, by decide, by decide, pass468_2339, rfl⟩
def src469 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,4,2,1,307664,16⟩
private theorem pass469_2293 : (Triangular src469) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass469_2295 : (Triangular src469) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass469_2301 : (Triangular src469) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass469_2318 : (Triangular src469) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass469_2366 : (Triangular src469) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover469 : Cover (Triangular src469) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass469_2293, by decide, by decide, pass469_2295, by decide, by decide, pass469_2301, by decide, by decide, pass469_2318, by decide, by decide, pass469_2366, rfl⟩
def src470 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,4,2,1,307664,16⟩
private theorem pass470_2293 : (Triangular src470) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass470_2299 : (Triangular src470) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass470_2316 : (Triangular src470) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass470_2364 : (Triangular src470) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover470 : Cover (Triangular src470) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass470_2293, by decide, by decide, pass470_2299, by decide, by decide, pass470_2316, by decide, by decide, pass470_2364, rfl⟩
def src471 : Request := ⟨⟨⟨2600,3628,783,115771⟩,527755772952576,4745819470168⟩,8,2,1,307664,16⟩
private theorem pass471_2293 : (Triangular src471) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass471_2297 : (Triangular src471) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass471_2308 : (Triangular src471) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass471_2339 : (Triangular src471) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover471 : Cover (Triangular src471) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass471_2293, by decide, by decide, pass471_2297, by decide, by decide, pass471_2308, by decide, by decide, pass471_2339, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source0823

-- Source: Research6969.PrefixNormalDataSeed16
section Z6969Source0824
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed16
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,16⟩
  bank i := ![bank236 64247, bank245 72277, bank252 72277, bank252 81311, bank252 91474, bank245 102908, bank270 115771, bank302 130242, bank303 146522, bank332 185441, bank347 264035] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307664
  seedFloor := 16

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 64247
    · exact rank245 72277
    · exact rank252 72277
    · exact rank252 81311
    · exact rank252 91474
    · exact rank245 102908
    · exact rank270 115771
    · exact rank302 130242
    · exact rank303 146522
    · exact rank332 185441
    · exact rank347 264035
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover465⟩
    · exact ⟨_, cover466⟩
    · exact ⟨_, cover467⟩
    · exact ⟨_, cover468⟩
    · exact ⟨_, cover470⟩
    · exact ⟨_, cover469⟩
    · exact ⟨_, cover471⟩
    · exact ⟨_, cover472⟩
    · exact ⟨_, cover473⟩
    · exact ⟨_, cover474⟩
    · exact ⟨_, cover475⟩

def price : NormalPrice := ⟨16, 90/100, 80/100, ![3306312164160, 227103237392, 10688428608, 668038800], 11568344374968281⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal14 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal14.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal14.price
    plan price SmallCertificates.primary16 SmallCertificates.rescue16 where
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
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 16))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 16 ≤ seedDegree G)
    (floor : 307664 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary16 SmallCertificates.rescue16) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal14.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal14.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal14.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 16))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 16 ≤ seedDegree G)
    (floor : 307664 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary16 SmallCertificates.rescue16,
      P.mainGrade=335 ∧ P.rescueGrade=293 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal14.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal14.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal14.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed16
end Z6969Source0824

-- Source: Research6969.PrefixMainDataHighQuadraticFinal15
section Z6969Source0825
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal15
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 21
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 14, 14, 21, 21, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank30 1953, bank40 2218, bank50 2450, bank54 2755, bank62 3617, bank82 2965, bank84 5564, bank74 6544, bank116 3644, bank110 3824, bank168 4492, bank125 29117, bank153 6368, bank199 9241, bank181 61748, bank212 10770, bank174 148759, bank169 292467] i
  head := src1189
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  historyValues := [![14899, 166190, 770330, 3756021],
    ![12303, 132326, 598309, 2855804],
    ![53398/9, 573526/9, 598309, 2855804],
    ![29433/8, 307461/8, 927844/3, 12928492/9],
    ![63824/25, 662608/25, 408177/2, 3814209/4],
    ![72196/49, 749862/49, 3379354/25, 15601412/25],
    ![81680/81, 838540/81, 944128/9, 4308325/9],
    ![89110/121, 925560/121, 4194856/49, 19378670/49],
    ![89110/121, 925560/121, 4194856/49, 19378670/49],
    ![89110/121, 925560/121, 4194856/49, 351649],
    ![63754/121, 3115676/441, 543881/8, 351649],
    ![61324/121, 3115676/441, 543881/8, 351649],
    ![61324/121, 748432/121, 119341/2, 51263792/225],
    ![61324/121, 741853/121, 117349/2, 51263792/225],
    ![61324/121, 741853/121, 117349/2, 5044516/25],
    ![675632/1681, 741853/121, 117349/2, 5044516/25],
    ![675632/1681, 9225904/1681, 2448496/49, 5044516/25],
    ![675632/1681, 6729280/1323, 30291556/675, 130002388/675],
    ![474397/1369, 6729280/1323, 30291556/675, 130002388/675],
    ![474397/1369, 13473803/2738, 219708/5, 530293260/2809],
    ![462882/1369, 13473803/2738, 219708/5, 530293260/2809],
    ![459151/1369, 13473803/2738, 219708/5, 530293260/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 17 307566 := by
  refine ⟨?_, rank154 7034, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1189⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free30_0
    · exact free40_0
    · exact free50_0
    · exact free54_0
    · exact free62_0
    · exact free82_0
    · exact free84_0
    · exact free74_2
    · exact free116_1
    · exact free110_0
    · exact free168_0
    · exact free125_0
    · exact free153_0
    · exact free199_0
    · exact free181_0
    · exact free212_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [335802046, 334603366, 335761934, 334961960, 335691360, 333549253, 334702775, 165881465, 166211283, 163411391, 160886776, 161032276, 94700938, 112102856, 69956224, 65970644, 87755331, 99654816, 99749563, 124576937, 171915788, 233740661], [1026173, 1029458, 1026283, 1028475, 1026476, 1032347, 1029185, 2302828, 2297344, 2343896, 2385871, 2383452, 4178300, 3505020, 5729589, 6089691, 4528522, 3969221, 3965222, 3135561, 2209165, 1581879],
  ![124074217672020, 1607297341504, 210366594900, 4723372990], 182978269490810060⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 13473803/2738, 219708/5, 530293260/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal15
end Z6969Source0825

-- Source: Research6969.PrefixNormalDataSeed17
section Z6969Source0826
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed17
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,17⟩
  bank i := ![bank245 57109, bank245 64247, bank245 72277, bank245 81311, bank245 91474, bank252 102908, bank270 102908, bank303 115771, bank303 130242, bank332 164837, bank347 234698] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307566
  seedFloor := 17

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 57109
    · exact rank245 64247
    · exact rank245 72277
    · exact rank245 81311
    · exact rank245 91474
    · exact rank252 102908
    · exact rank270 102908
    · exact rank303 115771
    · exact rank303 130242
    · exact rank332 164837
    · exact rank347 234698
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover454⟩
    · exact ⟨_, cover455⟩
    · exact ⟨_, cover456⟩
    · exact ⟨_, cover457⟩
    · exact ⟨_, cover458⟩
    · exact ⟨_, cover459⟩
    · exact ⟨_, cover460⟩
    · exact ⟨_, cover461⟩
    · exact ⟨_, cover462⟩
    · exact ⟨_, cover463⟩
    · exact ⟨_, cover464⟩

def price : NormalPrice := ⟨17, 90/100, 80/100, ![3512956674420, 228381675604, 11356455396, 668038800], 10976346647019908⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal15 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal15.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal15.price
    plan price SmallCertificates.primary17 SmallCertificates.rescue17 where
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
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 17))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 17 ≤ seedDegree G)
    (floor : 307566 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary17 SmallCertificates.rescue17) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal15.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal15.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal15.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 17))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 17 ≤ seedDegree G)
    (floor : 307566 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary17 SmallCertificates.rescue17,
      P.mainGrade=335 ∧ P.rescueGrade=293 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal15.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal15.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal15.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed17
end Z6969Source0826

-- Source: Research6969.PrefixMainDataHighQuadraticFinal16
section Z6969Source0827
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal16
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 16, 21, 17, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank98 3253, bank137 3540, bank168 4492, bank126 26574, bank153 6368, bank199 9241, bank185 48641, bank212 10770, bank175 125592, bank169 292467] i
  head := src1188
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![14984, 166091, 772092, 3763989],
    ![12303, 131471, 1188923/2, 2817234],
    ![53398/9, 569821/9, 1188923/2, 2817234],
    ![29433/8, 610837/16, 2765102/9, 1417098],
    ![16211/9, 707443/36, 3223481/16, 15564177/16],
    ![18775/16, 791175/64, 396682/3, 644809],
    ![89110/121, 919385/121, 4166926/49, 19116945/49],
    ![89110/121, 919385/121, 5354323/72, 12837889/36],
    ![63754/121, 3099146/441, 543881/8, 12837889/36],
    ![63754/121, 3099146/441, 543881/8, 10582009/36],
    ![63754/121, 759156/121, 252225/4, 1091736/5],
    ![63754/121, 759156/121, 9185560/147, 5044516/25],
    ![1355575/3362, 759156/121, 9185560/147, 5044516/25],
    ![1355575/3362, 9159784/1681, 2448496/49, 5044516/25],
    ![1355575/3362, 6680830/1323, 30075146/675, 4749874/25],
    ![480830/1369, 6680830/1323, 30075146/675, 4749874/25],
    ![480830/1369, 26756751/5476, 219708/5, 523131210/2809],
    ![929061/2738, 26756751/5476, 219708/5, 523131210/2809],
    ![459151/1369, 26756751/5476, 219708/5, 523131210/2809]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 18 307462 := by
  refine ⟨?_, rank154 6939, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1188⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free98_0
    · exact free137_0
    · exact free168_0
    · exact free126_0
    · exact free153_0
    · exact free199_0
    · exact free185_0
    · exact free212_0
    · exact free175_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [335216398, 332883294, 335134975, 333149596, 332571944, 333193919, 153760756, 153553789, 153521054, 153410196, 111163540, 72223288, 69720100, 87437547, 101419491, 101477070, 116992213, 172121095, 233626203], [1027778, 1034172, 1028001, 1033442, 1035025, 1033321, 2504350, 2507792, 2508336, 2510179, 3537627, 5549409, 5749906, 4544547, 3894742, 3892312, 3347586, 2206690, 1582820],
  ![124013461076460, 1607420963052, 210263582700, 4635437940], 182711329596118984⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 26756751/5476, 219708/5, 523131210/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal16
end Z6969Source0827

-- Source: Research6969.PrefixNormalDataSeed18
section Z6969Source0828
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed18
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,18⟩
  bank i := ![bank236 50764, bank245 57109, bank245 64247, bank252 64247, bank252 72277, bank245 81311, bank270 91474, bank303 102908, bank303 115771, bank347 208621, bank332 264035] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 32, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307462
  seedFloor := 18

theorem sources : plan.Sources 2293 2389 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 50764
    · exact rank245 57109
    · exact rank245 64247
    · exact rank252 64247
    · exact rank252 72277
    · exact rank245 81311
    · exact rank270 91474
    · exact rank303 102908
    · exact rank303 115771
    · exact rank347 208621
    · exact rank332 264035
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover443⟩
    · exact ⟨_, cover444⟩
    · exact ⟨_, cover445⟩
    · exact ⟨_, cover446⟩
    · exact ⟨_, cover448⟩
    · exact ⟨_, cover447⟩
    · exact ⟨_, cover449⟩
    · exact ⟨_, cover450⟩
    · exact ⟨_, cover451⟩
    · exact ⟨_, cover453⟩
    · exact ⟨_, cover452⟩

def price : NormalPrice := ⟨18, 85/100, 80/100, ![3719601184680, 229660113816, 12024482184, 668038800], 9262048418821099⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal16 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal16.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal16.price
    plan price SmallCertificates.primary18 SmallCertificates.rescue18 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 246
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
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 18))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 18 ≤ seedDegree G)
    (floor : 307462 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary18 SmallCertificates.rescue18) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal16.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal16.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal16.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 18))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 18 ≤ seedDegree G)
    (floor : 307462 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary18 SmallCertificates.rescue18,
      P.mainGrade=335 ∧ P.rescueGrade=246 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal16.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal16.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal16.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed18
end Z6969Source0828

-- Source: Research6969.PrefixNormalCatalogue
section Z6969Source0829
set_option autoImplicit true
namespace Research6969.TransitionPacket.NormalCatalogue
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14 (Equation)
open K1_14_3 (ProjectedProduct SeedField)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Lower6960 Research6966
open Far6969RescueGeometry (Model Family word)
open scoped Classical
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

abbrev seed (i : Fin 18) : ℕ := i.val+1
def floor (i : Fin 18) : ℕ := ![308417, 308410, 308395, 308374, 308347, 308315, 308276, 308232, 308182, 308125, 308063, 307995, 307921, 307841, 307755, 307664, 307566, 307462] i
def savedMainGrade (i : Fin 18) : ℕ := ![335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335] i
def savedRescueGrade (i : Fin 18) : ℕ := ![386, 387, 387, 315, 319, 319, 371, 387, 319, 315, 319, 319, 256, 293, 293, 293, 293, 246] i
def mainBook (i : Fin 18) : JointLedger.Book := ![SmallCertificates.primary1, SmallCertificates.primary2, SmallCertificates.primary3, SmallCertificates.primary4, SmallCertificates.primary5, SmallCertificates.primary6, SmallCertificates.primary7, SmallCertificates.primary8, SmallCertificates.primary9, SmallCertificates.primary10, SmallCertificates.primary11, SmallCertificates.primary12, SmallCertificates.primary13, SmallCertificates.primary14, SmallCertificates.primary15, SmallCertificates.primary16, SmallCertificates.primary17, SmallCertificates.primary18] i
def rescueBook (i : Fin 18) : JointLedger.Book := ![SmallCertificates.rescue1, SmallCertificates.rescue2, SmallCertificates.rescue3, SmallCertificates.rescue4, SmallCertificates.rescue5, SmallCertificates.rescue6, SmallCertificates.rescue7, SmallCertificates.rescue8, SmallCertificates.rescue9, SmallCertificates.rescue10, SmallCertificates.rescue11, SmallCertificates.rescue12, SmallCertificates.rescue13, SmallCertificates.rescue14, SmallCertificates.rescue15, SmallCertificates.rescue16, SmallCertificates.rescue17, SmallCertificates.rescue18] i


theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (i : Fin 18)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j k, (D.block j).eval (nodeL k) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (Prefix6969Rescue.graphShape 2 (seed i)))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed_lower : seed i ≤ seedDegree G)
    (physical : floor i ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Pair F Crt G (mainBook i) (rescueBook i)) := by
  fin_cases i
  · exact NormalPrefixData.Seed1.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed2.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed3.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed4.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed5.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed6.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed7.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed8.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed9.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed10.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed11.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed12.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed13.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed14.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed15.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed16.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed17.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed18.packet F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical

theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (i : Fin 18)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j k, (D.block j).eval (nodeL k) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (Prefix6969Rescue.graphShape 2 (seed i)))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed_lower : seed i ≤ seedDegree G)
    (physical : floor i ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G (mainBook i) (rescueBook i),
      P.mainGrade=savedMainGrade i ∧ P.rescueGrade=savedRescueGrade i := by
  fin_cases i
  · exact NormalPrefixData.Seed1.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed2.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed3.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed4.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed5.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed6.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed7.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed8.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed9.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed10.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed11.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed12.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed13.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed14.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed15.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed16.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed17.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical
  · exact NormalPrefixData.Seed18.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical


theorem small_bill (i : Fin 18) :
    ∀ j k : Fin 22, j.val+k.val ≤ 21 →
      JointLedger.Pass (mainBook i) (rescueBook i) (JointRouted.seedWeight 133460 (seed i))
      (JointRouted.ordWeight 133460 1) 274784969259510674 j.val k.val := by
  fin_cases i
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary1 SmallCertificates.rescue1
      (JointRouted.seedWeight 133460 1) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price1, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill1
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary2 SmallCertificates.rescue2
      (JointRouted.seedWeight 133460 2) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price2, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill2
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary3 SmallCertificates.rescue3
      (JointRouted.seedWeight 133460 3) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price3, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill3
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary4 SmallCertificates.rescue4
      (JointRouted.seedWeight 133460 4) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price4, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill4
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary5 SmallCertificates.rescue5
      (JointRouted.seedWeight 133460 5) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price5, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill5
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary6 SmallCertificates.rescue6
      (JointRouted.seedWeight 133460 6) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price6, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill6
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary7 SmallCertificates.rescue7
      (JointRouted.seedWeight 133460 7) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price7, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill7
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary8 SmallCertificates.rescue8
      (JointRouted.seedWeight 133460 8) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price8, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill8
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary9 SmallCertificates.rescue9
      (JointRouted.seedWeight 133460 9) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price9, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill9
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary10 SmallCertificates.rescue10
      (JointRouted.seedWeight 133460 10) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price10, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill10
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary11 SmallCertificates.rescue11
      (JointRouted.seedWeight 133460 11) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price11, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill11
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary12 SmallCertificates.rescue12
      (JointRouted.seedWeight 133460 12) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price12, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill12
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary13 SmallCertificates.rescue13
      (JointRouted.seedWeight 133460 13) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price13, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill13
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary14 SmallCertificates.rescue14
      (JointRouted.seedWeight 133460 14) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price14, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill14
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary15 SmallCertificates.rescue15
      (JointRouted.seedWeight 133460 15) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price15, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill15
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary16 SmallCertificates.rescue16
      (JointRouted.seedWeight 133460 16) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price16, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill16
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary17 SmallCertificates.rescue17
      (JointRouted.seedWeight 133460 17) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price17, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill17
  · change ∀ a b : Fin 22, a.val+b.val ≤ 21 → JointLedger.Pass
      SmallCertificates.primary18 SmallCertificates.rescue18
      (JointRouted.seedWeight 133460 18) (JointRouted.ordWeight 133460 1) 274784969259510674 a.val b.val
    rw [SmallCertificates.seed_price18, SmallCertificates.ordinate_price]
    exact SmallCertificates.bill18

theorem reduce {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet}
    (i : Fin 18) (P : Pair F Crt G (mainBook i) (rescueBook i))
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (prime : Prime G) (slope : G.natDegree = 1) (degree : 2 ≤ jetDegree G)
    (caps : RowCaps G (Prefix6969Rescue.graphShape 2 (seed i))) :
    Γ.card≤274784969259510674 ∨ ∃ (f : Equation) (H : Pade.Row SeedField),
      ProjectedProduct (P.main∪P.rescue) f ∧ 22≤f.natDegree ∧ H.primitive ∧
      H.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (H.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue))
        (TransitionClassification.content (TransitionClassification.band f.natDegree)) := by
  have equal : jetDegree G = 2 := Nat.le_antisymm
    ((K1_14_2_2_2_1.jetDegree_le G 2).mpr fun j k hn => (caps j k hn).1) degree
  have width (j k : ℕ) : ((G.coeff j).coeff k).totalDegree ≤ seed i := by
    by_cases zero : (G.coeff j).coeff k = 0
    · simp [zero]
    · exact (caps j k zero).2.2
  have phys : 131071+M.overhead ≤ (133460 : ℤ) := by omega
  have msmall : 41*(mainBook i).seedMass < K1.p := by fin_cases i <;> decide +kernel
  have rsmall : 41*(rescueBook i).seedMass < K1.p := by fin_cases i <;> decide +kernel
  have table : ∀ j k : Fin 22, j.val+k.val ≤ 21 →
      JointLedger.Pass (mainBook i) (rescueBook i) (JointRouted.seedWeight 133460 (seed i))
      (JointRouted.ordWeight 133460 (jetDegree G-1)) 274784969259510674 j.val k.val := by
    simpa only [equal, show 2-1=1 by decide] using small_bill i
  exact P.reduce lo (hi.trans (by decide)) prime slope degree (Nat.succ_pos i.val) width
    (by decide : 0<133460) phys (by decide) (by decide) msmall rsmall table



end
end Research6969.TransitionPacket.NormalCatalogue
end Z6969Source0829

-- Source: Research6969.PrefixNearModel
section Z6969Source0830
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family)
open Prefix6969Rescue (graphShape)
open Research6969 Research6966
open Research6969.TransitionPacket (Pair)
open Research6969.TransitionPacket.NormalCatalogue (mainBook rescueBook savedMainGrade savedRescueGrade)

abbrev NormalSeed := Research6969.TransitionPacket.NormalCatalogue.seed
abbrev NormalFloor := Research6969.TransitionPacket.NormalCatalogue.floor

inductive Outcome {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) : Type where
  | ordinary : Packet F Crt nearFee nearOrd nearSeed nearGrade nearWidth → Outcome F Crt
  | quadratic19 : Packet F Crt 232149228686438842 124136401111740 1817642895608 336 4851 → Outcome F Crt
  | cubicWide : Packet F Crt 231540946588816362 120708380414700 1818807159480 336 4150 → Outcome F Crt
  | quinticMid : Packet F Crt 230343569625208500 121629787325460 1818493958952 336 4321 → Outcome F Crt
  | normal (i : Fin 18) (G : Jet) (prime : Prime G) (slope : G.natDegree=1)
      (degree : 2≤jetDegree G) (caps : RowCaps G (graphShape 2 (NormalSeed i)))
      (seedExact : seedDegree G=NormalSeed i)
      (packet : Pair F Crt G (mainBook i) (rescueBook i))
      (mainGrade : packet.mainGrade=savedMainGrade i) (rescueGrade : packet.rescueGrade=savedRescueGrade i) : Outcome F Crt

private def into56 (i : Fin 18) : Fin 56 := ⟨i.val,i.isLt.trans (by decide)⟩
private theorem floor_dom (i : Fin 18) : NormalFloor i≤threshold (into56 i) := by
  fin_cases i <;> decide +kernel

/-- The outer helper's actual degree, seed interval, and physical weight
choose between the native light/ordinary, early, and normal packets. -/
theorem route_using
    (choose : ∀ (a : Fin 6) (j : Fin 56), UniformAllowed (a.val+2) (seed j) →
      ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧
        w≤(if a.val=0 then threshold j else (a.val+2)*128682-1) ∧
        ∃ c : NearCase (a.val+2) l u w, c.uniform)
    {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Outcome F Crt) := by
  obtain ⟨R, unit | ⟨phys, common, slope, jd, jmax, sd, smax, jbound, floor⟩⟩ :=
    Prefix6969NearOuter.split F Crt lo hi noPole residues
  · obtain ⟨P⟩:=Prefix6969NearOuter.ordinary R hi noPole residues (Or.inl unit)
    exact ⟨.ordinary P⟩
  let G := R.out.exception
  have prime : Prime G := Prefix6969MiddleTransfer.prime_of_irred common.1
  by_cases affine : jetDegree G=1
  · obtain ⟨P⟩:=Prefix6969NearOuter.ordinary R hi noPole residues (Or.inr ⟨prime,slope,affine,smax⟩)
    exact ⟨.ordinary P⟩
  change 1≤jetDegree G at jd
  change jetDegree G≤7 at jmax
  change 1≤seedDegree G at sd
  have nonlin : 2≤jetDegree G := by omega
  have sm : seedDegree G≤56 := jbound nonlin
  let a : Fin 6 := ⟨jetDegree G-2,by omega⟩
  let j : Fin 56 := ⟨seedDegree G-1,by omega⟩
  have ae : a.val+2=jetDegree G := by dsimp [a]; omega
  have se : seed j=seedDegree G := by dsimp [seed,j]; omega
  let W := RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw
  have high : jetDegree G=2 → threshold j≤W → Nonempty (Outcome F Crt) := by
    intro quad enough
    by_cases sm18 : seedDegree G≤18
    · let i : Fin 18 := ⟨seedDegree G-1,by omega⟩
      have ise : NormalSeed i=seedDegree G := by dsimp [NormalSeed,i]; omega
      have ie : into56 i=j := Fin.ext rfl
      have physical := (floor_dom i).trans (ie.symm ▸ enough)
      have shape : RowCaps G (graphShape 2 (NormalSeed i)) := by
        intro s k hn
        have h : G.coeff s≠0 := fun eq=>hn (by simp [eq])
        exact ⟨(K1_14_2_2_2_1.jetDegree_le G 2).mp quad.le s k hn,
          (le_natDegree_of_ne_zero h).trans slope.le,
          (K1_14_2_2_2_1.seedDegree_le G _).mp ise.ge s k⟩
      obtain ⟨P,mr,rr⟩ := TransitionPacket.NormalCatalogue.packet_with_grades
        F Crt i lo hi noPole residues phys prime slope common.2.2.1 shape common
        quad.ge ise.le physical
      exact ⟨.normal i G prime slope quad.ge shape ise.symm P mr rr⟩
    by_cases seed19 : seedDegree G=19
    · have j19 : j=(18:Fin 56) := by apply Fin.ext; dsimp [j]; omega
      have physical : 307353≤W := by rw [j19] at enough; exact enough
      obtain ⟨P⟩ := NearSavedQuadraticSingletons0.data.run F Crt lo hi noPole residues
        phys common slope quad (by decide) seed19.ge seed19.le physical
      rw [NearSavedQuadraticSingletons0.fee_exact] at P
      exact ⟨.quadratic19 P⟩
    have allowed : UniformAllowed (a.val+2) (seed j) := by
      rw [ae,se,quad]
      unfold UniformAllowed
      omega
    obtain ⟨l,h,w,lower,upper,physfit,c,pay⟩ := choose a j allowed
    have first : a.val=0 := by omega
    have physical : w≤W := (by simpa only [if_pos first] using physfit : w≤threshold j).trans enough
    obtain ⟨P⟩ := c.run F Crt lo hi noPole residues phys common slope ae.symm
      (by omega) (se ▸ lower) (se ▸ upper) physical
    obtain ⟨Q⟩ := P.reprice pay.1 pay.2.1 pay.2.2
    exact ⟨.ordinary Q⟩
  by_cases quad : jetDegree G=2
  · by_cases low : W<threshold j
    · obtain ⟨P⟩ := light_packet F Crt lo hi noPole residues phys common slope quad j sd se.ge low
      exact ⟨.ordinary P⟩
    · exact high quad (Nat.le_of_not_gt low)
  by_cases cubic : jetDegree G=3 ∧ 41≤seedDegree G
  · have fw : 386045≤W := by have t:=floor; change jetDegree G*128682-1≤W at t; rwa [cubic.1] at t
    obtain ⟨P⟩ := NearSavedRepricedHelperCases0.data.run F Crt lo hi noPole residues phys common slope
      cubic.1 (by decide) cubic.2 sm fw
    rw [NearSavedRepricedHelperCases0.fee_exact] at P
    exact ⟨.cubicWide P⟩
  by_cases quintic : jetDegree G=5 ∧ 26≤seedDegree G ∧ seedDegree G≤40
  · have fw : 643409≤W := by have t:=floor; change jetDegree G*128682-1≤W at t; rwa [quintic.1] at t
    obtain ⟨P⟩ := NearSavedRepricedHelperCases1.data.run F Crt lo hi noPole residues phys common slope
      quintic.1 (by decide) quintic.2.1 quintic.2.2 fw
    rw [NearSavedRepricedHelperCases1.fee_exact] at P
    exact ⟨.quinticMid P⟩
  have allowed : UniformAllowed (a.val+2) (seed j) := by
    rw [ae,se]
    unfold UniformAllowed
    omega
  obtain ⟨l,h,w,lower,upper,physfit,c,pay⟩ := choose a j allowed
  have nz : a.val≠0 := by omega
  have physical : w≤W := by
    simp only [if_neg nz,ae] at physfit
    exact physfit.trans floor
  obtain ⟨P⟩ := c.run F Crt lo hi noPole residues phys common slope ae.symm
    (by omega) (se ▸ lower) (se ▸ upper) physical
  obtain ⟨Q⟩ := P.reprice pay.1 pay.2.1 pay.2.2
  exact ⟨.ordinary Q⟩

end
end Lower6960.Prefix6969Early
end Z6969Source0830

-- Source: Research6969.TerminalLedger
section Z6969Source0831
set_option autoImplicit true
namespace Research6969.TerminalLedger

/-- Charge the two seed coordinates together. The narrower axis is also
bounded by the total seed degree, even when one of the net coefficients
is negative after applying the prefix credits. -/
theorem clipped_axes (c k v x cap narrow:ℤ) (nonneg:0≤k) (vx:x≤v)
    (vCap:v≤cap) (xCap:x≤narrow) (xn:0≤x):
    c*v+k*x ≤ max 0 c*cap + (max 0 (c+k)-max 0 c)*min narrow cap := by
  let base:=max 0 c
  let peak:=max 0 (c+k)
  have bb:0≤base:=le_max_left .. 
  have p:base≤peak:=max_le_max_left _ (by omega)
  have off:=mul_le_mul_of_nonneg_right (le_max_right 0 c) (show 0≤v-x by omega)
  have on:=mul_le_mul_of_nonneg_right (le_max_right 0 (c+k)) xn
  have main:=mul_le_mul_of_nonneg_left vCap bb
  have side:=mul_le_mul_of_nonneg_left (le_min xCap (vx.trans vCap)) (sub_nonneg.mpr p)
  dsimp [base,peak] at main side
  linarith only [off,on,main,side]

theorem choose_degree (coefficient i lo hi : ℤ) (lower : lo ≤ i) (upper : i ≤ hi) :
    coefficient * i ≤ coefficient * (if 0 ≤ coefficient then hi else lo) := by
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left upper h
  · exact mul_le_mul_of_nonpos_left lower (le_of_not_ge h)

/-- One ledger for every ordinary native, affine, surface and rectangular
tariff. Its result charges only the excess over the actual terminal degrees
already paid by the prefix. -/
theorem split_cost (marks inside outside deg offDegree v w axis:ℤ)
    (gradeLo gradeHi seedMax narrowMax totalSeed:ℤ)
    (creditDegree creditSeed rawOff offTail constant ordinate seed axisRate:ℤ)
    (split:marks=inside+outside)
    (onFee:inside≤constant+ordinate*deg+seed*v+axisRate*axis)
    (offFee:outside≤rawOff*w+offTail)
    (bounds:gradeLo≤deg ∧ deg≤gradeHi ∧ v≤seedMax ∧ axis≤narrowMax ∧ axis≤v)
    (source:v+w≤totalSeed) (wn:0≤w) (xn:0≤axis) (dn:0≤offDegree)
    (ordNonneg:0≤creditDegree) (axisNonneg:0≤axisRate):
    let off:=max 0 (rawOff-creditSeed)
    let c:=seed-creditSeed-off
    marks-creditDegree*(deg+offDegree)-creditSeed*(v+w) ≤
      off*totalSeed+offTail+constant+
      (ordinate-creditDegree)*(if 0≤ordinate-creditDegree then gradeHi else gradeLo)+
      max 0 c*seedMax+(max 0 (c+axisRate)-max 0 c)*min narrowMax seedMax := by
  intro off c
  obtain ⟨dl,dh,vc,ac,av⟩:=bounds
  have offN:0≤off:=le_max_left .. 
  have x1:=mul_le_mul_of_nonneg_right (le_max_right 0 (rawOff-creditSeed)) wn
  have x2:=mul_le_mul_of_nonneg_left source offN
  have y:=choose_degree (ordinate-creditDegree) deg gradeLo gradeHi dl dh
  have z:=clipped_axes c axisRate v axis seedMax narrowMax axisNonneg av vc ac xn
  have free:=mul_nonneg ordNonneg dn
  change (rawOff-creditSeed)*w≤off*w at x1
  dsimp only [c] at z ⊢
  linarith only [split,onFee,offFee,x1,x2,y,z,free]

end Research6969.TerminalLedger
end Z6969Source0831

-- Source: Research6969.GraphPartition
section Z6969Source0832
set_option autoImplicit true
namespace Research6969.GraphPartition
noncomputable section
open K1 (I K p)
open K1_14 (Jet Equation Seeds FX jetAt atX graphEval)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (mass Active)
open K1_14_3 (Surface SeedField Parent)
open Research6966
open NearBook (owning outside ownerSources otherSources split_mass)
open PadeNativeQuotient (Native)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 1100000
set_option maxRecDepth 7000

abbrev On {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ} (F:P1.FamilyAt 179740 M Γ)
    (q:Surface) (z:K):Prop:=∀ P∈q.asIdeal,jetAt P (M.label z) (F.scalar z)=0

structure Split {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ} (F:P1.FamilyAt 179740 M Γ)
    (T:Finset K) (S:Finset Surface) (G:Jet) where
  onEq:Equation
  offEq:Equation
  onLabels:Finset K
  offLabels:Finset K
  onProduct:JointProjection.Product (owning G S) onEq
  offProduct:JointProjection.Product (outside G S) offEq
  onSub:onLabels⊆T
  offSub:offLabels⊆T
  size:onLabels.card+offLabels.card=T.card
  onMarks:∀z∈onLabels,∃q∈owning G S,On F q z
  offMarks:∀z∈offLabels,∃q∈outside G S,On F q z

theorem exists_split {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ} (F:P1.FamilyAt 179740 M Γ)
    (T:Finset K) (S:Finset Surface) (G:Jet) (geo:∀q∈S,Parent q) (cover:∀z∈T,∃q∈S,On F q z):
    Nonempty (Split F T S G) := by
  classical
  obtain ⟨a,pa⟩:=JointProjection.exists_product (owning G S) (fun q h=>geo q (mem_filter.mp h).1)
  obtain ⟨b,pb⟩:=JointProjection.exists_product (outside G S) (fun q h=>geo q (mem_filter.mp h).1)
  let owned:=T.filter fun z=>∃q∈owning G S,On F q z
  have sub:owned⊆T:=filter_subset _ _
  refine ⟨⟨a,b,owned,T\owned,pa,pb,sub,sdiff_subset,?_,fun z hz=>(mem_filter.mp hz).2,?_⟩⟩
  · rw [Nat.add_comm];exact card_sdiff_add_card_eq_card sub
  · intro z hz
    obtain ⟨present,off⟩:=mem_sdiff.mp hz
    obtain ⟨q,hq,mark⟩:=cover z present
    refine ⟨q,mem_filter.mpr ⟨hq,?_⟩,mark⟩
    intro hit
    exact off (mem_filter.mpr ⟨present,q,mem_filter.mpr ⟨hq,hit⟩,mark⟩)

theorem measured {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ T S G} {F:P1.FamilyAt 179740 M Γ}
    (P:Split F T S G) (sources:Finset (Ideal Ambient)) (active:∀J∈sources,Active J)
    (origins:∀q∈S,∃J∈sources,q.asIdeal=J.comap toJet):
    P.onEq.natDegree+P.offEq.natDegree≤mass sources 0 ∧
      K1_14_4.seedDegree P.onEq+K1_14_4.seedDegree P.offEq≤mass sources 1 := by
  have geomA:=JointProjection.measures P.onProduct (ownerSources G sources)
    (fun Q h=>active Q (mem_filter.mp h).1) (by
      intro q h
      obtain ⟨Q,hQ,eq⟩:=origins q (mem_filter.mp h).1
      exact ⟨Q,mem_filter.mpr ⟨hQ,by have own: G∈q.asIdeal:=(mem_filter.mp h).2;rwa [eq] at own⟩,eq⟩)
  have geomB:=JointProjection.measures P.offProduct (otherSources G sources)
    (fun Q h=>active Q (mem_filter.mp h).1) (by
      intro q h
      obtain ⟨Q,hQ,eq⟩:=origins q (mem_filter.mp h).1
      exact ⟨Q,mem_filter.mpr ⟨hQ,by have off: G∉q.asIdeal:=(mem_filter.mp h).2;rwa [eq] at off⟩,eq⟩)
  exact ⟨(Nat.add_le_add geomA.1 geomB.1).trans_eq (split_mass ..),(Nat.add_le_add geomA.2 geomB.2).trans_eq (split_mass ..)⟩

theorem labels_root {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ T S G} {F:P1.FamilyAt 179740 M Γ}
    (P:Split F T S G):
    (∀z∈P.onLabels,(P.onEq.map (graphEval (M.label z))).eval (atX (F.scalar z))=0) ∧
    (∀z∈P.offLabels,(P.offEq.map (graphEval (M.label z))).eval (atX (F.scalar z))=0) := by
  constructor
  · intro z hz
    obtain ⟨q,hq,on⟩:=P.onMarks z hz
    have src:=on (C P.onEq) (P.onProduct.vanishes hq)
    simpa [jetAt,Polynomial.eval_map] using src
  · intro z hz
    obtain ⟨q,hq,on⟩:=P.offMarks z hz
    have src:=on (C P.offEq) (P.offProduct.vanishes hq)
    simpa [jetAt,Polynomial.eval_map] using src

end
end Research6969.GraphPartition
end Z6969Source0832

import ProximityPrize.SubmissionLower.R6970Height2313Rescue
import ProximityPrize.SubmissionLower.R6970Height2313Sources

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0816
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed13
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,2,1,13⟩
  bank i := ![Physical.src498.bank, Physical.src499.bank, Physical.src500.bank, Physical.src501.bank, Physical.src502.bank, Physical.src503.bank, Physical.src505.bank, Physical.src504.bank, Physical.src506.bank, Physical.src507.bank] i
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

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank498
    · exact Physical.rank499
    · exact Physical.rank500
    · exact Physical.rank501
    · exact Physical.rank502
    · exact Physical.rank503
    · exact Physical.rank505
    · exact Physical.rank504
    · exact Physical.rank506
    · exact Physical.rank507
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover498⟩
    · exact ⟨_, Physical.cover499⟩
    · exact ⟨_, Physical.cover500⟩
    · exact ⟨_, Physical.cover501⟩
    · exact ⟨_, Physical.cover502⟩
    · exact ⟨_, Physical.cover503⟩
    · exact ⟨_, Physical.cover505⟩
    · exact ⟨_, Physical.cover504⟩
    · exact ⟨_, Physical.cover506⟩
    · exact ⟨_, Physical.cover507⟩

def price : NormalPrice := ⟨13, 6225506901011179/6663225626066944, 860115/1048102, ![2684999032200, 223153223640, 7309113450, 562249500], 17254611247749744⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

end Research6969.NormalPrefixData.Seed13
end Z6969Source0816


section Z6969Source0819
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed14
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,14⟩
  bank i := ![Physical.src487.bank, Physical.src488.bank, Physical.src489.bank, Physical.src491.bank, Physical.src490.bank, Physical.src492.bank, Physical.src494.bank, Physical.src493.bank, Physical.src495.bank, Physical.src496.bank, Physical.src497.bank] i
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

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank487
    · exact Physical.rank488
    · exact Physical.rank489
    · exact Physical.rank491
    · exact Physical.rank490
    · exact Physical.rank492
    · exact Physical.rank494
    · exact Physical.rank493
    · exact Physical.rank495
    · exact Physical.rank496
    · exact Physical.rank497
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover487⟩
    · exact ⟨_, Physical.cover488⟩
    · exact ⟨_, Physical.cover489⟩
    · exact ⟨_, Physical.cover491⟩
    · exact ⟨_, Physical.cover490⟩
    · exact ⟨_, Physical.cover492⟩
    · exact ⟨_, Physical.cover494⟩
    · exact ⟨_, Physical.cover493⟩
    · exact ⟨_, Physical.cover495⟩
    · exact ⟨_, Physical.cover496⟩
    · exact ⟨_, Physical.cover497⟩

def price : NormalPrice := ⟨14, 200918836244299/220319602180096, 865721/1039665, ![2891536847640, 224431001768, 9347570232, 667695600], 16664588119877961⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

end Research6969.NormalPrefixData.Seed14
end Z6969Source0819


section Z6969Source0821
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed15
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,15⟩
  bank i := ![Physical.src476.bank, Physical.src477.bank, Physical.src479.bank, Physical.src478.bank, Physical.src481.bank, Physical.src480.bank, Physical.src482.bank, Physical.src483.bank, Physical.src484.bank, Physical.src485.bank, Physical.src486.bank] i
  reserve i := ![0, 1, 3, 3, 4, 4, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307754
  seedFloor := 15

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank476
    · exact Physical.rank477
    · exact Physical.rank479
    · exact Physical.rank478
    · exact Physical.rank481
    · exact Physical.rank480
    · exact Physical.rank482
    · exact Physical.rank483
    · exact Physical.rank484
    · exact Physical.rank485
    · exact Physical.rank486
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover476⟩
    · exact ⟨_, Physical.cover477⟩
    · exact ⟨_, Physical.cover479⟩
    · exact ⟨_, Physical.cover478⟩
    · exact ⟨_, Physical.cover481⟩
    · exact ⟨_, Physical.cover480⟩
    · exact ⟨_, Physical.cover482⟩
    · exact ⟨_, Physical.cover483⟩
    · exact ⟨_, Physical.cover484⟩
    · exact ⟨_, Physical.cover485⟩
    · exact ⟨_, Physical.cover486⟩

def price : NormalPrice := ⟨15, 5563322728555097/6068387176251392, 198119/238634, ![3098075193900, 225708783180, 10015253820, 667695600], 14949526028609773⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

end Research6969.NormalPrefixData.Seed15
end Z6969Source0821


section Z6969Source0824
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed16
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,16⟩
  bank i := ![Physical.src465.bank, Physical.src466.bank, Physical.src467.bank, Physical.src468.bank, Physical.src470.bank, Physical.src469.bank, Physical.src471.bank, Physical.src472.bank, Physical.src473.bank, Physical.src474.bank, Physical.src475.bank] i
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

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank465
    · exact Physical.rank466
    · exact Physical.rank467
    · exact Physical.rank468
    · exact Physical.rank470
    · exact Physical.rank469
    · exact Physical.rank471
    · exact Physical.rank472
    · exact Physical.rank473
    · exact Physical.rank474
    · exact Physical.rank475
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover465⟩
    · exact ⟨_, Physical.cover466⟩
    · exact ⟨_, Physical.cover467⟩
    · exact ⟨_, Physical.cover468⟩
    · exact ⟨_, Physical.cover470⟩
    · exact ⟨_, Physical.cover469⟩
    · exact ⟨_, Physical.cover471⟩
    · exact ⟨_, Physical.cover472⟩
    · exact ⟨_, Physical.cover473⟩
    · exact ⟨_, Physical.cover474⟩
    · exact ⟨_, Physical.cover475⟩

def price : NormalPrice := ⟨16, 2493245173832569/2762614100721664, 261373280092821131207941/316125164402176917372928, ![3304613540160, 226986564592, 10682937408, 667695600], 13268884849188488⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

end Research6969.NormalPrefixData.Seed16
end Z6969Source0824


section Z6969Source0826
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed17
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,17⟩
  bank i := ![Physical.src454.bank, Physical.src455.bank, Physical.src456.bank, Physical.src457.bank, Physical.src458.bank, Physical.src459.bank, Physical.src460.bank, Physical.src461.bank, Physical.src462.bank, Physical.src463.bank, Physical.src464.bank] i
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

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank454
    · exact Physical.rank455
    · exact Physical.rank456
    · exact Physical.rank457
    · exact Physical.rank458
    · exact Physical.rank459
    · exact Physical.rank460
    · exact Physical.rank461
    · exact Physical.rank462
    · exact Physical.rank463
    · exact Physical.rank464
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover454⟩
    · exact ⟨_, Physical.cover455⟩
    · exact ⟨_, Physical.cover456⟩
    · exact ⟨_, Physical.cover457⟩
    · exact ⟨_, Physical.cover458⟩
    · exact ⟨_, Physical.cover459⟩
    · exact ⟨_, Physical.cover460⟩
    · exact ⟨_, Physical.cover461⟩
    · exact ⟨_, Physical.cover462⟩
    · exact ⟨_, Physical.cover463⟩
    · exact ⟨_, Physical.cover464⟩

def price : NormalPrice := ⟨17, 1746890482697078306266547/1960804737984294889193472, 48379/60249, ![3511151355600, 228264342720, 11350619280, 667695600], 11655159682270253⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

end Research6969.NormalPrefixData.Seed17
end Z6969Source0826


section Z6969Source0828
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed18
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,18⟩
  bank i := ![Physical.src443.bank, Physical.src444.bank, Physical.src445.bank, Physical.src446.bank, Physical.src448.bank, Physical.src447.bank, Physical.src449.bank, Physical.src450.bank, Physical.src451.bank, Physical.src453.bank, Physical.src452.bank] i
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

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank443
    · exact Physical.rank444
    · exact Physical.rank445
    · exact Physical.rank446
    · exact Physical.rank448
    · exact Physical.rank447
    · exact Physical.rank449
    · exact Physical.rank450
    · exact Physical.rank451
    · exact Physical.rank453
    · exact Physical.rank452
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover443⟩
    · exact ⟨_, Physical.cover444⟩
    · exact ⟨_, Physical.cover445⟩
    · exact ⟨_, Physical.cover446⟩
    · exact ⟨_, Physical.cover448⟩
    · exact ⟨_, Physical.cover447⟩
    · exact ⟨_, Physical.cover449⟩
    · exact ⟨_, Physical.cover450⟩
    · exact ⟨_, Physical.cover451⟩
    · exact ⟨_, Physical.cover453⟩
    · exact ⟨_, Physical.cover452⟩

def price : NormalPrice := ⟨18, 3873805721900947/4479890187354112, 464054/576549, ![3717689701860, 229542124132, 12018302868, 667695600], 10354916837205900⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

end Research6969.NormalPrefixData.Seed18
end Z6969Source0828


end Research6970.Height2313

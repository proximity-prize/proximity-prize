import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.SeedTwoRescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src618 := _root_.Research6970.Height2313.Physical.src618
private theorem rank618 : P3_7_1.BankOK src618.bank := _root_.Research6970.Height2313.Physical.rank618
private theorem cover618 : Cover (Triangular src618) 2313 2308 _root_.Research6970.Height2313.Physical.ends618 :=
  _root_.Research6970.Height2313.Physical.cover618

private abbrev src619 := _root_.Research6970.Height2313.Physical.src619
private theorem rank619 : P3_7_1.BankOK src619.bank := _root_.Research6970.Height2313.Physical.rank619
private theorem cover619 : Cover (Triangular src619) 2313 2308 _root_.Research6970.Height2313.Physical.ends619 :=
  _root_.Research6970.Height2313.Physical.cover619

private abbrev src620 := _root_.Research6970.Height2313.Physical.src620
private theorem rank620 : P3_7_1.BankOK src620.bank := _root_.Research6970.Height2313.Physical.rank620
private theorem cover620 : Cover (Triangular src620) 2313 2308 _root_.Research6970.Height2313.Physical.ends620 :=
  _root_.Research6970.Height2313.Physical.cover620

private abbrev src621 := _root_.Research6970.Height2313.Physical.src621
private theorem rank621 : P3_7_1.BankOK src621.bank := _root_.Research6970.Height2313.Physical.rank621
private theorem cover621 : Cover (Triangular src621) 2313 2308 _root_.Research6970.Height2313.Physical.ends621 :=
  _root_.Research6970.Height2313.Physical.cover621

private abbrev src623 := _root_.Research6970.Height2313.Physical.src623
private theorem rank623 : P3_7_1.BankOK src623.bank := _root_.Research6970.Height2313.Physical.rank623
private theorem cover623 : Cover (Triangular src623) 2313 2308 _root_.Research6970.Height2313.Physical.ends623 :=
  _root_.Research6970.Height2313.Physical.cover623

private abbrev src622 := _root_.Research6970.Height2313.Physical.src622
private theorem rank622 : P3_7_1.BankOK src622.bank := _root_.Research6970.Height2313.Physical.rank622
private theorem cover622 : Cover (Triangular src622) 2313 2308 _root_.Research6970.Height2313.Physical.ends622 :=
  _root_.Research6970.Height2313.Physical.cover622

private abbrev src624 := _root_.Research6970.Height2313.Physical.src624
private theorem rank624 : P3_7_1.BankOK src624.bank := _root_.Research6970.Height2313.Physical.rank624
private theorem cover624 : Cover (Triangular src624) 2313 2308 _root_.Research6970.Height2313.Physical.ends624 :=
  _root_.Research6970.Height2313.Physical.cover624

private abbrev src625 := _root_.Research6970.Height2313.Physical.src625
private theorem rank625 : P3_7_1.BankOK src625.bank := _root_.Research6970.Height2313.Physical.rank625
private theorem cover625 : Cover (Triangular src625) 2313 2308 _root_.Research6970.Height2313.Physical.ends625 :=
  _root_.Research6970.Height2313.Physical.cover625

private abbrev src626 := _root_.Research6970.Height2313.Physical.src626
private theorem rank626 : P3_7_1.BankOK src626.bank := _root_.Research6970.Height2313.Physical.rank626
private theorem cover626 : Cover (Triangular src626) 2313 2308 _root_.Research6970.Height2313.Physical.ends626 :=
  _root_.Research6970.Height2313.Physical.cover626

private abbrev src627 := _root_.Research6970.Height2313.Physical.src627
private theorem rank627 : P3_7_1.BankOK src627.bank := _root_.Research6970.Height2313.Physical.rank627
private theorem cover627 : Cover (Triangular src627) 2313 2308 _root_.Research6970.Height2313.Physical.ends627 :=
  _root_.Research6970.Height2313.Physical.cover627

private abbrev src628 := _root_.Research6970.Height2313.Physical.src628
private theorem rank628 : P3_7_1.BankOK src628.bank := _root_.Research6970.Height2313.Physical.rank628
private theorem cover628 : Cover (Triangular src628) 2313 2308 _root_.Research6970.Height2313.Physical.ends628 :=
  _root_.Research6970.Height2313.Physical.cover628

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,2⟩
  bank f := ![src618.bank, src619.bank, src620.bank, src621.bank, src623.bank, src622.bank, src624.bank, src625.bank, src626.bank, src627.bank, src628.bank] f
  reserve f := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 27] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308378
  seedFloor := 2

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank618
    · exact rank619
    · exact rank620
    · exact rank621
    · exact rank623
    · exact rank622
    · exact rank624
    · exact rank625
    · exact rank626
    · exact rank627
    · exact rank628
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover618⟩
    · exact ⟨_, cover619⟩
    · exact ⟨_, cover620⟩
    · exact ⟨_, cover621⟩
    · exact ⟨_, cover623⟩
    · exact ⟨_, cover622⟩
    · exact ⟨_, cover624⟩
    · exact ⟨_, cover625⟩
    · exact ⟨_, cover626⟩
    · exact ⟨_, cover627⟩
    · exact ⟨_, cover628⟩

def price : TransferPrice := ⟨2, ![499017450260, 254259668590, 6161563435, 651353400], 38879759036669888⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.SeedTwoRescue

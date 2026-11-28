import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed10Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src530 := _root_.Research6970.Height2313.Physical.src530
private theorem rank530 : P3_7_1.BankOK src530.bank := _root_.Research6970.Height2313.Physical.rank530
private theorem cover530 : Cover (Triangular src530) 2313 2308 _root_.Research6970.Height2313.Physical.ends530 :=
  _root_.Research6970.Height2313.Physical.cover530

private abbrev src531 := _root_.Research6970.Height2313.Physical.src531
private theorem rank531 : P3_7_1.BankOK src531.bank := _root_.Research6970.Height2313.Physical.rank531
private theorem cover531 : Cover (Triangular src531) 2313 2308 _root_.Research6970.Height2313.Physical.ends531 :=
  _root_.Research6970.Height2313.Physical.cover531

private abbrev src532 := _root_.Research6970.Height2313.Physical.src532
private theorem rank532 : P3_7_1.BankOK src532.bank := _root_.Research6970.Height2313.Physical.rank532
private theorem cover532 : Cover (Triangular src532) 2313 2308 _root_.Research6970.Height2313.Physical.ends532 :=
  _root_.Research6970.Height2313.Physical.cover532

private abbrev src533 := _root_.Research6970.Height2313.Physical.src533
private theorem rank533 : P3_7_1.BankOK src533.bank := _root_.Research6970.Height2313.Physical.rank533
private theorem cover533 : Cover (Triangular src533) 2313 2308 _root_.Research6970.Height2313.Physical.ends533 :=
  _root_.Research6970.Height2313.Physical.cover533

private abbrev src535 := _root_.Research6970.Height2313.Physical.src535
private theorem rank535 : P3_7_1.BankOK src535.bank := _root_.Research6970.Height2313.Physical.rank535
private theorem cover535 : Cover (Triangular src535) 2313 2308 _root_.Research6970.Height2313.Physical.ends535 :=
  _root_.Research6970.Height2313.Physical.cover535

private abbrev src534 := _root_.Research6970.Height2313.Physical.src534
private theorem rank534 : P3_7_1.BankOK src534.bank := _root_.Research6970.Height2313.Physical.rank534
private theorem cover534 : Cover (Triangular src534) 2313 2308 _root_.Research6970.Height2313.Physical.ends534 :=
  _root_.Research6970.Height2313.Physical.cover534

private abbrev src536 := _root_.Research6970.Height2313.Physical.src536
private theorem rank536 : P3_7_1.BankOK src536.bank := _root_.Research6970.Height2313.Physical.rank536
private theorem cover536 : Cover (Triangular src536) 2313 2308 _root_.Research6970.Height2313.Physical.ends536 :=
  _root_.Research6970.Height2313.Physical.cover536

private abbrev src538 := _root_.Research6970.Height2313.Physical.src538
private theorem rank538 : P3_7_1.BankOK src538.bank := _root_.Research6970.Height2313.Physical.rank538
private theorem cover538 : Cover (Triangular src538) 2313 2308 _root_.Research6970.Height2313.Physical.ends538 :=
  _root_.Research6970.Height2313.Physical.cover538

private abbrev src539 := _root_.Research6970.Height2313.Physical.src539
private theorem rank539 : P3_7_1.BankOK src539.bank := _root_.Research6970.Height2313.Physical.rank539
private theorem cover539 : Cover (Triangular src539) 2313 2308 _root_.Research6970.Height2313.Physical.ends539 :=
  _root_.Research6970.Height2313.Physical.cover539

private abbrev src537 := _root_.Research6970.Height2313.Physical.src537
private theorem rank537 : P3_7_1.BankOK src537.bank := _root_.Research6970.Height2313.Physical.rank537
private theorem cover537 : Cover (Triangular src537) 2313 2308 _root_.Research6970.Height2313.Physical.ends537 :=
  _root_.Research6970.Height2313.Physical.cover537

private abbrev src540 := _root_.Research6970.Height2313.Physical.src540
private theorem rank540 : P3_7_1.BankOK src540.bank := _root_.Research6970.Height2313.Physical.rank540
private theorem cover540 : Cover (Triangular src540) 2313 2308 _root_.Research6970.Height2313.Physical.ends540 :=
  _root_.Research6970.Height2313.Physical.cover540

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,10⟩
  bank f := ![src530.bank, src531.bank, src532.bank, src533.bank, src535.bank, src534.bank, src536.bank, src538.bank, src539.bank, src537.bank, src540.bank] f
  reserve f := ![0, 1, 2, 4, 6, 6, 10, 13, 16, 13, 20] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308107
  seedFloor := 10

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank530
    · exact rank531
    · exact rank532
    · exact rank533
    · exact rank535
    · exact rank534
    · exact rank536
    · exact rank538
    · exact rank539
    · exact rank537
    · exact rank540
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover530⟩
    · exact ⟨_, cover531⟩
    · exact ⟨_, cover532⟩
    · exact ⟨_, cover533⟩
    · exact ⟨_, cover535⟩
    · exact ⟨_, cover534⟩
    · exact ⟨_, cover536⟩
    · exact ⟨_, cover538⟩
    · exact ⟨_, cover539⟩
    · exact ⟨_, cover537⟩
    · exact ⟨_, cover540⟩

def price : TransferPrice := ⟨10, ![2065383993420, 219319879404, 5622395295, 562249500], 22078481995425635⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed10Rescue

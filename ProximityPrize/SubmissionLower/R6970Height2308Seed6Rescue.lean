import ProximityPrize.SubmissionLower.Bundle6970_0d932b1d02cdb0ad
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed6Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src574 := _root_.Research6970.Height2313.Physical.src574
private theorem rank574 : P3_7_1.BankOK src574.bank := _root_.Research6970.Height2313.Physical.rank574
private theorem cover574 : Cover (Triangular src574) 2313 2308 _root_.Research6970.Height2313.Physical.ends574 :=
  _root_.Research6970.Height2313.Physical.cover574

private abbrev src575 := _root_.Research6970.Height2313.Physical.src575
private theorem rank575 : P3_7_1.BankOK src575.bank := _root_.Research6970.Height2313.Physical.rank575
private theorem cover575 : Cover (Triangular src575) 2313 2308 _root_.Research6970.Height2313.Physical.ends575 :=
  _root_.Research6970.Height2313.Physical.cover575

private abbrev src576 := _root_.Research6970.Height2313.Physical.src576
private theorem rank576 : P3_7_1.BankOK src576.bank := _root_.Research6970.Height2313.Physical.rank576
private theorem cover576 : Cover (Triangular src576) 2313 2308 _root_.Research6970.Height2313.Physical.ends576 :=
  _root_.Research6970.Height2313.Physical.cover576

private abbrev src577 := _root_.Research6970.Height2313.Physical.src577
private theorem rank577 : P3_7_1.BankOK src577.bank := _root_.Research6970.Height2313.Physical.rank577
private theorem cover577 : Cover (Triangular src577) 2313 2308 _root_.Research6970.Height2313.Physical.ends577 :=
  _root_.Research6970.Height2313.Physical.cover577

private abbrev src578 := _root_.Research6970.Height2313.Physical.src578
private theorem rank578 : P3_7_1.BankOK src578.bank := _root_.Research6970.Height2313.Physical.rank578
private theorem cover578 : Cover (Triangular src578) 2313 2308 _root_.Research6970.Height2313.Physical.ends578 :=
  _root_.Research6970.Height2313.Physical.cover578

private abbrev src579 := _root_.Research6970.Height2313.Physical.src579
private theorem rank579 : P3_7_1.BankOK src579.bank := _root_.Research6970.Height2313.Physical.rank579
private theorem cover579 : Cover (Triangular src579) 2313 2308 _root_.Research6970.Height2313.Physical.ends579 :=
  _root_.Research6970.Height2313.Physical.cover579

private abbrev src580 := _root_.Research6970.Height2313.Physical.src580
private theorem rank580 : P3_7_1.BankOK src580.bank := _root_.Research6970.Height2313.Physical.rank580
private theorem cover580 : Cover (Triangular src580) 2313 2308 _root_.Research6970.Height2313.Physical.ends580 :=
  _root_.Research6970.Height2313.Physical.cover580

private abbrev src581 := _root_.Research6970.Height2313.Physical.src581
private theorem rank581 : P3_7_1.BankOK src581.bank := _root_.Research6970.Height2313.Physical.rank581
private theorem cover581 : Cover (Triangular src581) 2313 2308 _root_.Research6970.Height2313.Physical.ends581 :=
  _root_.Research6970.Height2313.Physical.cover581

private abbrev src582 := _root_.Research6970.Height2313.Physical.src582
private theorem rank582 : P3_7_1.BankOK src582.bank := _root_.Research6970.Height2313.Physical.rank582
private theorem cover582 : Cover (Triangular src582) 2313 2308 _root_.Research6970.Height2313.Physical.ends582 :=
  _root_.Research6970.Height2313.Physical.cover582

private abbrev src583 := _root_.Research6970.Height2313.Physical.src583
private theorem rank583 : P3_7_1.BankOK src583.bank := _root_.Research6970.Height2313.Physical.rank583
private theorem cover583 : Cover (Triangular src583) 2313 2308 _root_.Research6970.Height2313.Physical.ends583 :=
  _root_.Research6970.Height2313.Physical.cover583

private abbrev src584 := _root_.Research6970.Height2313.Physical.src584
private theorem rank584 : P3_7_1.BankOK src584.bank := _root_.Research6970.Height2313.Physical.rank584
private theorem cover584 : Cover (Triangular src584) 2313 2308 _root_.Research6970.Height2313.Physical.ends584 :=
  _root_.Research6970.Height2313.Physical.cover584

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,6⟩
  bank f := ![src574.bank, src575.bank, src576.bank, src577.bank, src578.bank, src579.bank, src580.bank, src581.bank, src582.bank, src583.bank, src584.bank] f
  reserve f := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 32] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308288
  seedFloor := 6

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank574
    · exact rank575
    · exact rank576
    · exact rank577
    · exact rank578
    · exact rank579
    · exact rank580
    · exact rank581
    · exact rank582
    · exact rank583
    · exact rank584
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover574⟩
    · exact ⟨_, cover575⟩
    · exact ⟨_, cover576⟩
    · exact ⟨_, cover577⟩
    · exact ⟨_, cover578⟩
    · exact ⟨_, cover579⟩
    · exact ⟨_, cover580⟩
    · exact ⟨_, cover581⟩
    · exact ⟨_, cover582⟩
    · exact ⟨_, cover583⟩
    · exact ⟨_, cover584⟩

def price : TransferPrice := ⟨6, ![1374932697267, 245697307824, 5137502189, 757188600], 30312519092147357⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed6Rescue

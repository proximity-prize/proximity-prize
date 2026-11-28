import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed11Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src519 := _root_.Research6970.Height2313.Physical.src519
private theorem rank519 : P3_7_1.BankOK src519.bank := _root_.Research6970.Height2313.Physical.rank519
private theorem cover519 : Cover (Triangular src519) 2313 2308 _root_.Research6970.Height2313.Physical.ends519 :=
  _root_.Research6970.Height2313.Physical.cover519

private abbrev src520 := _root_.Research6970.Height2313.Physical.src520
private theorem rank520 : P3_7_1.BankOK src520.bank := _root_.Research6970.Height2313.Physical.rank520
private theorem cover520 : Cover (Triangular src520) 2313 2308 _root_.Research6970.Height2313.Physical.ends520 :=
  _root_.Research6970.Height2313.Physical.cover520

private abbrev src522 := _root_.Research6970.Height2313.Physical.src522
private theorem rank522 : P3_7_1.BankOK src522.bank := _root_.Research6970.Height2313.Physical.rank522
private theorem cover522 : Cover (Triangular src522) 2313 2308 _root_.Research6970.Height2313.Physical.ends522 :=
  _root_.Research6970.Height2313.Physical.cover522

private abbrev src521 := _root_.Research6970.Height2313.Physical.src521
private theorem rank521 : P3_7_1.BankOK src521.bank := _root_.Research6970.Height2313.Physical.rank521
private theorem cover521 : Cover (Triangular src521) 2313 2308 _root_.Research6970.Height2313.Physical.ends521 :=
  _root_.Research6970.Height2313.Physical.cover521

private abbrev src523 := _root_.Research6970.Height2313.Physical.src523
private theorem rank523 : P3_7_1.BankOK src523.bank := _root_.Research6970.Height2313.Physical.rank523
private theorem cover523 : Cover (Triangular src523) 2313 2308 _root_.Research6970.Height2313.Physical.ends523 :=
  _root_.Research6970.Height2313.Physical.cover523

private abbrev src524 := _root_.Research6970.Height2313.Physical.src524
private theorem rank524 : P3_7_1.BankOK src524.bank := _root_.Research6970.Height2313.Physical.rank524
private theorem cover524 : Cover (Triangular src524) 2313 2308 _root_.Research6970.Height2313.Physical.ends524 :=
  _root_.Research6970.Height2313.Physical.cover524

private abbrev src525 := _root_.Research6970.Height2313.Physical.src525
private theorem rank525 : P3_7_1.BankOK src525.bank := _root_.Research6970.Height2313.Physical.rank525
private theorem cover525 : Cover (Triangular src525) 2313 2308 _root_.Research6970.Height2313.Physical.ends525 :=
  _root_.Research6970.Height2313.Physical.cover525

private abbrev src527 := _root_.Research6970.Height2313.Physical.src527
private theorem rank527 : P3_7_1.BankOK src527.bank := _root_.Research6970.Height2313.Physical.rank527
private theorem cover527 : Cover (Triangular src527) 2313 2308 _root_.Research6970.Height2313.Physical.ends527 :=
  _root_.Research6970.Height2313.Physical.cover527

private abbrev src528 := _root_.Research6970.Height2313.Physical.src528
private theorem rank528 : P3_7_1.BankOK src528.bank := _root_.Research6970.Height2313.Physical.rank528
private theorem cover528 : Cover (Triangular src528) 2313 2308 _root_.Research6970.Height2313.Physical.ends528 :=
  _root_.Research6970.Height2313.Physical.cover528

private abbrev src526 := _root_.Research6970.Height2313.Physical.src526
private theorem rank526 : P3_7_1.BankOK src526.bank := _root_.Research6970.Height2313.Physical.rank526
private theorem cover526 : Cover (Triangular src526) 2313 2308 _root_.Research6970.Height2313.Physical.ends526 :=
  _root_.Research6970.Height2313.Physical.cover526

private abbrev src529 := _root_.Research6970.Height2313.Physical.src529
private theorem rank529 : P3_7_1.BankOK src529.bank := _root_.Research6970.Height2313.Physical.rank529
private theorem cover529 : Cover (Triangular src529) 2313 2308 _root_.Research6970.Height2313.Physical.ends529 :=
  _root_.Research6970.Height2313.Physical.cover529

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,11⟩
  bank f := ![src519.bank, src520.bank, src522.bank, src521.bank, src523.bank, src524.bank, src525.bank, src527.bank, src528.bank, src526.bank, src529.bank] f
  reserve f := ![0, 1, 3, 3, 4, 10, 10, 16, 20, 16, 25] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308048
  seedFloor := 11

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank519
    · exact rank520
    · exact rank522
    · exact rank521
    · exact rank523
    · exact rank524
    · exact rank525
    · exact rank527
    · exact rank528
    · exact rank526
    · exact rank529
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
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

def price : TransferPrice := ⟨11, ![2271922339680, 220597660816, 7344521184, 667695600], 22308455022227211⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed11Rescue

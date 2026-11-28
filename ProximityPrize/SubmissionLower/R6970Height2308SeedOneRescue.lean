import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.SeedOneRescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src629 := _root_.Research6970.Height2313.Physical.src629
private theorem rank629 : P3_7_1.BankOK src629.bank := _root_.Research6970.Height2313.Physical.rank629
private theorem cover629 : Cover (Triangular src629) 2313 2308 _root_.Research6970.Height2313.Physical.ends629 :=
  _root_.Research6970.Height2313.Physical.cover629

private abbrev src630 := _root_.Research6970.Height2313.Physical.src630
private theorem rank630 : P3_7_1.BankOK src630.bank := _root_.Research6970.Height2313.Physical.rank630
private theorem cover630 : Cover (Triangular src630) 2313 2308 _root_.Research6970.Height2313.Physical.ends630 :=
  _root_.Research6970.Height2313.Physical.cover630

private abbrev src631 := _root_.Research6970.Height2313.Physical.src631
private theorem rank631 : P3_7_1.BankOK src631.bank := _root_.Research6970.Height2313.Physical.rank631
private theorem cover631 : Cover (Triangular src631) 2313 2308 _root_.Research6970.Height2313.Physical.ends631 :=
  _root_.Research6970.Height2313.Physical.cover631

private abbrev src632 := _root_.Research6970.Height2313.Physical.src632
private theorem rank632 : P3_7_1.BankOK src632.bank := _root_.Research6970.Height2313.Physical.rank632
private theorem cover632 : Cover (Triangular src632) 2313 2308 _root_.Research6970.Height2313.Physical.ends632 :=
  _root_.Research6970.Height2313.Physical.cover632

private abbrev src633 := _root_.Research6970.Height2313.Physical.src633
private theorem rank633 : P3_7_1.BankOK src633.bank := _root_.Research6970.Height2313.Physical.rank633
private theorem cover633 : Cover (Triangular src633) 2313 2308 _root_.Research6970.Height2313.Physical.ends633 :=
  _root_.Research6970.Height2313.Physical.cover633

private abbrev src634 := _root_.Research6970.Height2313.Physical.src634
private theorem rank634 : P3_7_1.BankOK src634.bank := _root_.Research6970.Height2313.Physical.rank634
private theorem cover634 : Cover (Triangular src634) 2313 2308 _root_.Research6970.Height2313.Physical.ends634 :=
  _root_.Research6970.Height2313.Physical.cover634

private abbrev src635 := _root_.Research6970.Height2313.Physical.src635
private theorem rank635 : P3_7_1.BankOK src635.bank := _root_.Research6970.Height2313.Physical.rank635
private theorem cover635 : Cover (Triangular src635) 2313 2308 _root_.Research6970.Height2313.Physical.ends635 :=
  _root_.Research6970.Height2313.Physical.cover635

private abbrev src636 := _root_.Research6970.Height2313.Physical.src636
private theorem rank636 : P3_7_1.BankOK src636.bank := _root_.Research6970.Height2313.Physical.rank636
private theorem cover636 : Cover (Triangular src636) 2313 2308 _root_.Research6970.Height2313.Physical.ends636 :=
  _root_.Research6970.Height2313.Physical.cover636

private abbrev src638 := _root_.Research6970.Height2313.Physical.src638
private theorem rank638 : P3_7_1.BankOK src638.bank := _root_.Research6970.Height2313.Physical.rank638
private theorem cover638 : Cover (Triangular src638) 2313 2308 _root_.Research6970.Height2313.Physical.ends638 :=
  _root_.Research6970.Height2313.Physical.cover638

private abbrev src639 := _root_.Research6970.Height2313.Physical.src639
private theorem rank639 : P3_7_1.BankOK src639.bank := _root_.Research6970.Height2313.Physical.rank639
private theorem cover639 : Cover (Triangular src639) 2313 2308 _root_.Research6970.Height2313.Physical.ends639 :=
  _root_.Research6970.Height2313.Physical.cover639

private abbrev src637 := _root_.Research6970.Height2313.Physical.src637
private theorem rank637 : P3_7_1.BankOK src637.bank := _root_.Research6970.Height2313.Physical.rank637
private theorem cover637 : Cover (Triangular src637) 2313 2308 _root_.Research6970.Height2313.Physical.ends637 :=
  _root_.Research6970.Height2313.Physical.cover637

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,1⟩
  bank f := ![src629.bank, src630.bank, src631.bank, src632.bank, src633.bank, src634.bank, src635.bank, src636.bank, src638.bank, src639.bank, src637.bank] f
  reserve f := ![0, 1, 2, 3, 4, 6, 10, 10, 13, 22, 13] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308385
  seedFloor := 1

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank629
    · exact rank630
    · exact rank631
    · exact rank632
    · exact rank633
    · exact rank634
    · exact rank635
    · exact rank636
    · exact rank638
    · exact rank639
    · exact rank637
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover629⟩
    · exact ⟨_, cover630⟩
    · exact ⟨_, cover631⟩
    · exact ⟨_, cover632⟩
    · exact ⟨_, cover633⟩
    · exact ⟨_, cover634⟩
    · exact ⟨_, cover635⟩
    · exact ⟨_, cover636⟩
    · exact ⟨_, cover638⟩
    · exact ⟨_, cover639⟩
    · exact ⟨_, cover637⟩

def price : TransferPrice := ⟨1, ![228797207037, 230814104463, 552517740, 552522000], 40234908873553696⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.SeedOneRescue

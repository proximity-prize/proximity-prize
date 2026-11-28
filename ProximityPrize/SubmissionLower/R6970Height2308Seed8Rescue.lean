import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed8Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src552 := _root_.Research6970.Height2313.Physical.src552
private theorem rank552 : P3_7_1.BankOK src552.bank := _root_.Research6970.Height2313.Physical.rank552
private theorem cover552 : Cover (Triangular src552) 2313 2308 _root_.Research6970.Height2313.Physical.ends552 :=
  _root_.Research6970.Height2313.Physical.cover552

private abbrev src553 := _root_.Research6970.Height2313.Physical.src553
private theorem rank553 : P3_7_1.BankOK src553.bank := _root_.Research6970.Height2313.Physical.rank553
private theorem cover553 : Cover (Triangular src553) 2313 2308 _root_.Research6970.Height2313.Physical.ends553 :=
  _root_.Research6970.Height2313.Physical.cover553

private abbrev src554 := _root_.Research6970.Height2313.Physical.src554
private theorem rank554 : P3_7_1.BankOK src554.bank := _root_.Research6970.Height2313.Physical.rank554
private theorem cover554 : Cover (Triangular src554) 2313 2308 _root_.Research6970.Height2313.Physical.ends554 :=
  _root_.Research6970.Height2313.Physical.cover554

private abbrev src555 := _root_.Research6970.Height2313.Physical.src555
private theorem rank555 : P3_7_1.BankOK src555.bank := _root_.Research6970.Height2313.Physical.rank555
private theorem cover555 : Cover (Triangular src555) 2313 2308 _root_.Research6970.Height2313.Physical.ends555 :=
  _root_.Research6970.Height2313.Physical.cover555

private abbrev src557 := _root_.Research6970.Height2313.Physical.src557
private theorem rank557 : P3_7_1.BankOK src557.bank := _root_.Research6970.Height2313.Physical.rank557
private theorem cover557 : Cover (Triangular src557) 2313 2308 _root_.Research6970.Height2313.Physical.ends557 :=
  _root_.Research6970.Height2313.Physical.cover557

private abbrev src556 := _root_.Research6970.Height2313.Physical.src556
private theorem rank556 : P3_7_1.BankOK src556.bank := _root_.Research6970.Height2313.Physical.rank556
private theorem cover556 : Cover (Triangular src556) 2313 2308 _root_.Research6970.Height2313.Physical.ends556 :=
  _root_.Research6970.Height2313.Physical.cover556

private abbrev src558 := _root_.Research6970.Height2313.Physical.src558
private theorem rank558 : P3_7_1.BankOK src558.bank := _root_.Research6970.Height2313.Physical.rank558
private theorem cover558 : Cover (Triangular src558) 2313 2308 _root_.Research6970.Height2313.Physical.ends558 :=
  _root_.Research6970.Height2313.Physical.cover558

private abbrev src559 := _root_.Research6970.Height2313.Physical.src559
private theorem rank559 : P3_7_1.BankOK src559.bank := _root_.Research6970.Height2313.Physical.rank559
private theorem cover559 : Cover (Triangular src559) 2313 2308 _root_.Research6970.Height2313.Physical.ends559 :=
  _root_.Research6970.Height2313.Physical.cover559

private abbrev src560 := _root_.Research6970.Height2313.Physical.src560
private theorem rank560 : P3_7_1.BankOK src560.bank := _root_.Research6970.Height2313.Physical.rank560
private theorem cover560 : Cover (Triangular src560) 2313 2308 _root_.Research6970.Height2313.Physical.ends560 :=
  _root_.Research6970.Height2313.Physical.cover560

private abbrev src561 := _root_.Research6970.Height2313.Physical.src561
private theorem rank561 : P3_7_1.BankOK src561.bank := _root_.Research6970.Height2313.Physical.rank561
private theorem cover561 : Cover (Triangular src561) 2313 2308 _root_.Research6970.Height2313.Physical.ends561 :=
  _root_.Research6970.Height2313.Physical.cover561

private abbrev src562 := _root_.Research6970.Height2313.Physical.src562
private theorem rank562 : P3_7_1.BankOK src562.bank := _root_.Research6970.Height2313.Physical.rank562
private theorem cover562 : Cover (Triangular src562) 2313 2308 _root_.Research6970.Height2313.Physical.ends562 :=
  _root_.Research6970.Height2313.Physical.cover562

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,8⟩
  bank f := ![src552.bank, src553.bank, src554.bank, src555.bank, src557.bank, src556.bank, src558.bank, src559.bank, src560.bank, src561.bank, src562.bank] f
  reserve f := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 20] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308209
  seedFloor := 8

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank552
    · exact rank553
    · exact rank554
    · exact rank555
    · exact rank557
    · exact rank556
    · exact rank558
    · exact rank559
    · exact rank560
    · exact rank561
    · exact rank562
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover552⟩
    · exact ⟨_, cover553⟩
    · exact ⟨_, cover554⟩
    · exact ⟨_, cover555⟩
    · exact ⟨_, cover557⟩
    · exact ⟨_, cover556⟩
    · exact ⟨_, cover558⟩
    · exact ⟨_, cover559⟩
    · exact ⟨_, cover560⟩
    · exact ⟨_, cover561⟩
    · exact ⟨_, cover562⟩

def price : TransferPrice := ⟨8, ![1652307831720, 216764319864, 4668896543, 562249500], 25581769669513138⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed8Rescue

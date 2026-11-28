import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed12Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src508 := _root_.Research6970.Height2313.Physical.src508
private theorem rank508 : P3_7_1.BankOK src508.bank := _root_.Research6970.Height2313.Physical.rank508
private theorem cover508 : Cover (Triangular src508) 2313 2308 _root_.Research6970.Height2313.Physical.ends508 :=
  _root_.Research6970.Height2313.Physical.cover508

private abbrev src509 := _root_.Research6970.Height2313.Physical.src509
private theorem rank509 : P3_7_1.BankOK src509.bank := _root_.Research6970.Height2313.Physical.rank509
private theorem cover509 : Cover (Triangular src509) 2313 2308 _root_.Research6970.Height2313.Physical.ends509 :=
  _root_.Research6970.Height2313.Physical.cover509

private abbrev src510 := _root_.Research6970.Height2313.Physical.src510
private theorem rank510 : P3_7_1.BankOK src510.bank := _root_.Research6970.Height2313.Physical.rank510
private theorem cover510 : Cover (Triangular src510) 2313 2308 _root_.Research6970.Height2313.Physical.ends510 :=
  _root_.Research6970.Height2313.Physical.cover510

private abbrev src511 := _root_.Research6970.Height2313.Physical.src511
private theorem rank511 : P3_7_1.BankOK src511.bank := _root_.Research6970.Height2313.Physical.rank511
private theorem cover511 : Cover (Triangular src511) 2313 2308 _root_.Research6970.Height2313.Physical.ends511 :=
  _root_.Research6970.Height2313.Physical.cover511

private abbrev src512 := _root_.Research6970.Height2313.Physical.src512
private theorem rank512 : P3_7_1.BankOK src512.bank := _root_.Research6970.Height2313.Physical.rank512
private theorem cover512 : Cover (Triangular src512) 2313 2308 _root_.Research6970.Height2313.Physical.ends512 :=
  _root_.Research6970.Height2313.Physical.cover512

private abbrev src513 := _root_.Research6970.Height2313.Physical.src513
private theorem rank513 : P3_7_1.BankOK src513.bank := _root_.Research6970.Height2313.Physical.rank513
private theorem cover513 : Cover (Triangular src513) 2313 2308 _root_.Research6970.Height2313.Physical.ends513 :=
  _root_.Research6970.Height2313.Physical.cover513

private abbrev src514 := _root_.Research6970.Height2313.Physical.src514
private theorem rank514 : P3_7_1.BankOK src514.bank := _root_.Research6970.Height2313.Physical.rank514
private theorem cover514 : Cover (Triangular src514) 2313 2308 _root_.Research6970.Height2313.Physical.ends514 :=
  _root_.Research6970.Height2313.Physical.cover514

private abbrev src515 := _root_.Research6970.Height2313.Physical.src515
private theorem rank515 : P3_7_1.BankOK src515.bank := _root_.Research6970.Height2313.Physical.rank515
private theorem cover515 : Cover (Triangular src515) 2313 2308 _root_.Research6970.Height2313.Physical.ends515 :=
  _root_.Research6970.Height2313.Physical.cover515

private abbrev src516 := _root_.Research6970.Height2313.Physical.src516
private theorem rank516 : P3_7_1.BankOK src516.bank := _root_.Research6970.Height2313.Physical.rank516
private theorem cover516 : Cover (Triangular src516) 2313 2308 _root_.Research6970.Height2313.Physical.ends516 :=
  _root_.Research6970.Height2313.Physical.cover516

private abbrev src517 := _root_.Research6970.Height2313.Physical.src517
private theorem rank517 : P3_7_1.BankOK src517.bank := _root_.Research6970.Height2313.Physical.rank517
private theorem cover517 : Cover (Triangular src517) 2313 2308 _root_.Research6970.Height2313.Physical.ends517 :=
  _root_.Research6970.Height2313.Physical.cover517

private abbrev src518 := _root_.Research6970.Height2313.Physical.src518
private theorem rank518 : P3_7_1.BankOK src518.bank := _root_.Research6970.Height2313.Physical.rank518
private theorem cover518 : Cover (Triangular src518) 2313 2308 _root_.Research6970.Height2313.Physical.ends518 :=
  _root_.Research6970.Height2313.Physical.cover518

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,12⟩
  bank f := ![src508.bank, src509.bank, src510.bank, src511.bank, src512.bank, src513.bank, src514.bank, src515.bank, src516.bank, src517.bank, src518.bank] f
  reserve f := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 25] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307983
  seedFloor := 12

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank508
    · exact rank509
    · exact rank510
    · exact rank511
    · exact rank512
    · exact rank513
    · exact rank514
    · exact rank515
    · exact rank516
    · exact rank517
    · exact rank518
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
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

def price : TransferPrice := ⟨12, ![2478460685940, 221875442228, 8012204772, 667695600], 18838642937097636⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed12Rescue

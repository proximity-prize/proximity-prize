import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed4Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src596 := _root_.Research6970.Height2313.Physical.src596
private theorem rank596 : P3_7_1.BankOK src596.bank := _root_.Research6970.Height2313.Physical.rank596
private theorem cover596 : Cover (Triangular src596) 2313 2308 _root_.Research6970.Height2313.Physical.ends596 :=
  _root_.Research6970.Height2313.Physical.cover596

private abbrev src597 := _root_.Research6970.Height2313.Physical.src597
private theorem rank597 : P3_7_1.BankOK src597.bank := _root_.Research6970.Height2313.Physical.rank597
private theorem cover597 : Cover (Triangular src597) 2313 2308 _root_.Research6970.Height2313.Physical.ends597 :=
  _root_.Research6970.Height2313.Physical.cover597

private abbrev src598 := _root_.Research6970.Height2313.Physical.src598
private theorem rank598 : P3_7_1.BankOK src598.bank := _root_.Research6970.Height2313.Physical.rank598
private theorem cover598 : Cover (Triangular src598) 2313 2308 _root_.Research6970.Height2313.Physical.ends598 :=
  _root_.Research6970.Height2313.Physical.cover598

private abbrev src599 := _root_.Research6970.Height2313.Physical.src599
private theorem rank599 : P3_7_1.BankOK src599.bank := _root_.Research6970.Height2313.Physical.rank599
private theorem cover599 : Cover (Triangular src599) 2313 2308 _root_.Research6970.Height2313.Physical.ends599 :=
  _root_.Research6970.Height2313.Physical.cover599

private abbrev src601 := _root_.Research6970.Height2313.Physical.src601
private theorem rank601 : P3_7_1.BankOK src601.bank := _root_.Research6970.Height2313.Physical.rank601
private theorem cover601 : Cover (Triangular src601) 2313 2308 _root_.Research6970.Height2313.Physical.ends601 :=
  _root_.Research6970.Height2313.Physical.cover601

private abbrev src600 := _root_.Research6970.Height2313.Physical.src600
private theorem rank600 : P3_7_1.BankOK src600.bank := _root_.Research6970.Height2313.Physical.rank600
private theorem cover600 : Cover (Triangular src600) 2313 2308 _root_.Research6970.Height2313.Physical.ends600 :=
  _root_.Research6970.Height2313.Physical.cover600

private abbrev src602 := _root_.Research6970.Height2313.Physical.src602
private theorem rank602 : P3_7_1.BankOK src602.bank := _root_.Research6970.Height2313.Physical.rank602
private theorem cover602 : Cover (Triangular src602) 2313 2308 _root_.Research6970.Height2313.Physical.ends602 :=
  _root_.Research6970.Height2313.Physical.cover602

private abbrev src604 := _root_.Research6970.Height2313.Physical.src604
private theorem rank604 : P3_7_1.BankOK src604.bank := _root_.Research6970.Height2313.Physical.rank604
private theorem cover604 : Cover (Triangular src604) 2313 2308 _root_.Research6970.Height2313.Physical.ends604 :=
  _root_.Research6970.Height2313.Physical.cover604

private abbrev src605 := _root_.Research6970.Height2313.Physical.src605
private theorem rank605 : P3_7_1.BankOK src605.bank := _root_.Research6970.Height2313.Physical.rank605
private theorem cover605 : Cover (Triangular src605) 2313 2308 _root_.Research6970.Height2313.Physical.ends605 :=
  _root_.Research6970.Height2313.Physical.cover605

private abbrev src603 := _root_.Research6970.Height2313.Physical.src603
private theorem rank603 : P3_7_1.BankOK src603.bank := _root_.Research6970.Height2313.Physical.rank603
private theorem cover603 : Cover (Triangular src603) 2313 2308 _root_.Research6970.Height2313.Physical.ends603 :=
  _root_.Research6970.Height2313.Physical.cover603

private abbrev src606 := _root_.Research6970.Height2313.Physical.src606
private theorem rank606 : P3_7_1.BankOK src606.bank := _root_.Research6970.Height2313.Physical.rank606
private theorem cover606 : Cover (Triangular src606) 2313 2308 _root_.Research6970.Height2313.Physical.ends606 :=
  _root_.Research6970.Height2313.Physical.cover606

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,4⟩
  bank f := ![src596.bank, src597.bank, src598.bank, src599.bank, src601.bank, src600.bank, src602.bank, src604.bank, src605.bank, src603.bank, src606.bank] f
  reserve f := ![0, 1, 2, 4, 6, 6, 10, 13, 16, 13, 27] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308344
  seedFloor := 4

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank596
    · exact rank597
    · exact rank598
    · exact rank599
    · exact rank601
    · exact rank600
    · exact rank602
    · exact rank604
    · exact rank605
    · exact rank603
    · exact rank606
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover596⟩
    · exact ⟨_, cover597⟩
    · exact ⟨_, cover598⟩
    · exact ⟨_, cover599⟩
    · exact ⟨_, cover601⟩
    · exact ⟨_, cover600⟩
    · exact ⟨_, cover602⟩
    · exact ⟨_, cover604⟩
    · exact ⟨_, cover605⟩
    · exact ⟨_, cover603⟩
    · exact ⟨_, cover606⟩

def price : TransferPrice := ⟨4, ![907900461625, 236474205175, 5647548337, 651742500], 34068436498023103⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed4Rescue

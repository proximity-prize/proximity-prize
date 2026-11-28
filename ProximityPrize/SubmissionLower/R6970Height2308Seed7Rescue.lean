import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.Bundle6970_0d932b1d02cdb0ad
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed7Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src563 := _root_.Research6970.Height2313.Physical.src563
private theorem rank563 : P3_7_1.BankOK src563.bank := _root_.Research6970.Height2313.Physical.rank563
private theorem cover563 : Cover (Triangular src563) 2313 2308 _root_.Research6970.Height2313.Physical.ends563 :=
  _root_.Research6970.Height2313.Physical.cover563

private abbrev src564 := _root_.Research6970.Height2313.Physical.src564
private theorem rank564 : P3_7_1.BankOK src564.bank := _root_.Research6970.Height2313.Physical.rank564
private theorem cover564 : Cover (Triangular src564) 2313 2308 _root_.Research6970.Height2313.Physical.ends564 :=
  _root_.Research6970.Height2313.Physical.cover564

private abbrev src565 := _root_.Research6970.Height2313.Physical.src565
private theorem rank565 : P3_7_1.BankOK src565.bank := _root_.Research6970.Height2313.Physical.rank565
private theorem cover565 : Cover (Triangular src565) 2313 2308 _root_.Research6970.Height2313.Physical.ends565 :=
  _root_.Research6970.Height2313.Physical.cover565

private abbrev src566 := _root_.Research6970.Height2313.Physical.src566
private theorem rank566 : P3_7_1.BankOK src566.bank := _root_.Research6970.Height2313.Physical.rank566
private theorem cover566 : Cover (Triangular src566) 2313 2308 _root_.Research6970.Height2313.Physical.ends566 :=
  _root_.Research6970.Height2313.Physical.cover566

private abbrev src568 := _root_.Research6970.Height2313.Physical.src568
private theorem rank568 : P3_7_1.BankOK src568.bank := _root_.Research6970.Height2313.Physical.rank568
private theorem cover568 : Cover (Triangular src568) 2313 2308 _root_.Research6970.Height2313.Physical.ends568 :=
  _root_.Research6970.Height2313.Physical.cover568

private abbrev src567 := _root_.Research6970.Height2313.Physical.src567
private theorem rank567 : P3_7_1.BankOK src567.bank := _root_.Research6970.Height2313.Physical.rank567
private theorem cover567 : Cover (Triangular src567) 2313 2308 _root_.Research6970.Height2313.Physical.ends567 :=
  _root_.Research6970.Height2313.Physical.cover567

private abbrev src569 := _root_.Research6970.Height2313.Physical.src569
private theorem rank569 : P3_7_1.BankOK src569.bank := _root_.Research6970.Height2313.Physical.rank569
private theorem cover569 : Cover (Triangular src569) 2313 2308 _root_.Research6970.Height2313.Physical.ends569 :=
  _root_.Research6970.Height2313.Physical.cover569

private abbrev src570 := _root_.Research6970.Height2313.Physical.src570
private theorem rank570 : P3_7_1.BankOK src570.bank := _root_.Research6970.Height2313.Physical.rank570
private theorem cover570 : Cover (Triangular src570) 2313 2308 _root_.Research6970.Height2313.Physical.ends570 :=
  _root_.Research6970.Height2313.Physical.cover570

private abbrev src571 := _root_.Research6970.Height2313.Physical.src571
private theorem rank571 : P3_7_1.BankOK src571.bank := _root_.Research6970.Height2313.Physical.rank571
private theorem cover571 : Cover (Triangular src571) 2313 2308 _root_.Research6970.Height2313.Physical.ends571 :=
  _root_.Research6970.Height2313.Physical.cover571

private abbrev src572 := _root_.Research6970.Height2313.Physical.src572
private theorem rank572 : P3_7_1.BankOK src572.bank := _root_.Research6970.Height2313.Physical.rank572
private theorem cover572 : Cover (Triangular src572) 2313 2308 _root_.Research6970.Height2313.Physical.ends572 :=
  _root_.Research6970.Height2313.Physical.cover572

private abbrev src573 := _root_.Research6970.Height2313.Physical.src573
private theorem rank573 : P3_7_1.BankOK src573.bank := _root_.Research6970.Height2313.Physical.rank573
private theorem cover573 : Cover (Triangular src573) 2313 2308 _root_.Research6970.Height2313.Physical.ends573 :=
  _root_.Research6970.Height2313.Physical.cover573

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,7⟩
  bank f := ![src563.bank, src564.bank, src565.bank, src566.bank, src568.bank, src567.bank, src569.bank, src570.bank, src571.bank, src572.bank, src573.bank] f
  reserve f := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 32] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308251
  seedFloor := 7

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank563
    · exact rank564
    · exact rank565
    · exact rank566
    · exact rank568
    · exact rank567
    · exact rank569
    · exact rank570
    · exact rank571
    · exact rank572
    · exact rank573
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover563⟩
    · exact ⟨_, cover564⟩
    · exact ⟨_, cover565⟩
    · exact ⟨_, cover566⟩
    · exact ⟨_, cover568⟩
    · exact ⟨_, cover567⟩
    · exact ⟨_, cover569⟩
    · exact ⟨_, cover570⟩
    · exact ⟨_, cover571⟩
    · exact ⟨_, cover572⟩
    · exact ⟨_, cover573⟩

def price : TransferPrice := ⟨7, ![1522334094943, 236608267119, 5259373943, 751352100], 30754142137729235⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed7Rescue

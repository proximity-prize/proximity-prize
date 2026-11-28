import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed9Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src541 := _root_.Research6970.Height2313.Physical.src541
private theorem rank541 : P3_7_1.BankOK src541.bank := _root_.Research6970.Height2313.Physical.rank541
private theorem cover541 : Cover (Triangular src541) 2313 2308 _root_.Research6970.Height2313.Physical.ends541 :=
  _root_.Research6970.Height2313.Physical.cover541

private abbrev src542 := _root_.Research6970.Height2313.Physical.src542
private theorem rank542 : P3_7_1.BankOK src542.bank := _root_.Research6970.Height2313.Physical.rank542
private theorem cover542 : Cover (Triangular src542) 2313 2308 _root_.Research6970.Height2313.Physical.ends542 :=
  _root_.Research6970.Height2313.Physical.cover542

private abbrev src543 := _root_.Research6970.Height2313.Physical.src543
private theorem rank543 : P3_7_1.BankOK src543.bank := _root_.Research6970.Height2313.Physical.rank543
private theorem cover543 : Cover (Triangular src543) 2313 2308 _root_.Research6970.Height2313.Physical.ends543 :=
  _root_.Research6970.Height2313.Physical.cover543

private abbrev src544 := _root_.Research6970.Height2313.Physical.src544
private theorem rank544 : P3_7_1.BankOK src544.bank := _root_.Research6970.Height2313.Physical.rank544
private theorem cover544 : Cover (Triangular src544) 2313 2308 _root_.Research6970.Height2313.Physical.ends544 :=
  _root_.Research6970.Height2313.Physical.cover544

private abbrev src546 := _root_.Research6970.Height2313.Physical.src546
private theorem rank546 : P3_7_1.BankOK src546.bank := _root_.Research6970.Height2313.Physical.rank546
private theorem cover546 : Cover (Triangular src546) 2313 2308 _root_.Research6970.Height2313.Physical.ends546 :=
  _root_.Research6970.Height2313.Physical.cover546

private abbrev src545 := _root_.Research6970.Height2313.Physical.src545
private theorem rank545 : P3_7_1.BankOK src545.bank := _root_.Research6970.Height2313.Physical.rank545
private theorem cover545 : Cover (Triangular src545) 2313 2308 _root_.Research6970.Height2313.Physical.ends545 :=
  _root_.Research6970.Height2313.Physical.cover545

private abbrev src547 := _root_.Research6970.Height2313.Physical.src547
private theorem rank547 : P3_7_1.BankOK src547.bank := _root_.Research6970.Height2313.Physical.rank547
private theorem cover547 : Cover (Triangular src547) 2313 2308 _root_.Research6970.Height2313.Physical.ends547 :=
  _root_.Research6970.Height2313.Physical.cover547

private abbrev src548 := _root_.Research6970.Height2313.Physical.src548
private theorem rank548 : P3_7_1.BankOK src548.bank := _root_.Research6970.Height2313.Physical.rank548
private theorem cover548 : Cover (Triangular src548) 2313 2308 _root_.Research6970.Height2313.Physical.ends548 :=
  _root_.Research6970.Height2313.Physical.cover548

private abbrev src549 := _root_.Research6970.Height2313.Physical.src549
private theorem rank549 : P3_7_1.BankOK src549.bank := _root_.Research6970.Height2313.Physical.rank549
private theorem cover549 : Cover (Triangular src549) 2313 2308 _root_.Research6970.Height2313.Physical.ends549 :=
  _root_.Research6970.Height2313.Physical.cover549

private abbrev src551 := _root_.Research6970.Height2313.Physical.src551
private theorem rank551 : P3_7_1.BankOK src551.bank := _root_.Research6970.Height2313.Physical.rank551
private theorem cover551 : Cover (Triangular src551) 2313 2308 _root_.Research6970.Height2313.Physical.ends551 :=
  _root_.Research6970.Height2313.Physical.cover551

private abbrev src550 := _root_.Research6970.Height2313.Physical.src550
private theorem rank550 : P3_7_1.BankOK src550.bank := _root_.Research6970.Height2313.Physical.rank550
private theorem cover550 : Cover (Triangular src550) 2313 2308 _root_.Research6970.Height2313.Physical.ends550 :=
  _root_.Research6970.Height2313.Physical.cover550

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,9⟩
  bank f := ![src541.bank, src542.bank, src543.bank, src544.bank, src546.bank, src545.bank, src547.bank, src548.bank, src549.bank, src551.bank, src550.bank] f
  reserve f := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 27, 16] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308161
  seedFloor := 9

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank541
    · exact rank542
    · exact rank543
    · exact rank544
    · exact rank546
    · exact rank545
    · exact rank547
    · exact rank548
    · exact rank549
    · exact rank551
    · exact rank550
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover541⟩
    · exact ⟨_, cover542⟩
    · exact ⟨_, cover543⟩
    · exact ⟨_, cover544⟩
    · exact ⟨_, cover546⟩
    · exact ⟨_, cover545⟩
    · exact ⟨_, cover547⟩
    · exact ⟨_, cover548⟩
    · exact ⟨_, cover549⟩
    · exact ⟨_, cover551⟩
    · exact ⟨_, cover550⟩

def price : TransferPrice := ⟨9, ![1858846177980, 218042101276, 5802547223, 644738700], 26583047950369669⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed9Rescue

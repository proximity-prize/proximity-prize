import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.SeedThreeRescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src607 := _root_.Research6970.Height2313.Physical.src607
private theorem rank607 : P3_7_1.BankOK src607.bank := _root_.Research6970.Height2313.Physical.rank607
private theorem cover607 : Cover (Triangular src607) 2313 2308 _root_.Research6970.Height2313.Physical.ends607 :=
  _root_.Research6970.Height2313.Physical.cover607

private abbrev src608 := _root_.Research6970.Height2313.Physical.src608
private theorem rank608 : P3_7_1.BankOK src608.bank := _root_.Research6970.Height2313.Physical.rank608
private theorem cover608 : Cover (Triangular src608) 2313 2308 _root_.Research6970.Height2313.Physical.ends608 :=
  _root_.Research6970.Height2313.Physical.cover608

private abbrev src609 := _root_.Research6970.Height2313.Physical.src609
private theorem rank609 : P3_7_1.BankOK src609.bank := _root_.Research6970.Height2313.Physical.rank609
private theorem cover609 : Cover (Triangular src609) 2313 2308 _root_.Research6970.Height2313.Physical.ends609 :=
  _root_.Research6970.Height2313.Physical.cover609

private abbrev src610 := _root_.Research6970.Height2313.Physical.src610
private theorem rank610 : P3_7_1.BankOK src610.bank := _root_.Research6970.Height2313.Physical.rank610
private theorem cover610 : Cover (Triangular src610) 2313 2308 _root_.Research6970.Height2313.Physical.ends610 :=
  _root_.Research6970.Height2313.Physical.cover610

private abbrev src612 := _root_.Research6970.Height2313.Physical.src612
private theorem rank612 : P3_7_1.BankOK src612.bank := _root_.Research6970.Height2313.Physical.rank612
private theorem cover612 : Cover (Triangular src612) 2313 2308 _root_.Research6970.Height2313.Physical.ends612 :=
  _root_.Research6970.Height2313.Physical.cover612

private abbrev src611 := _root_.Research6970.Height2313.Physical.src611
private theorem rank611 : P3_7_1.BankOK src611.bank := _root_.Research6970.Height2313.Physical.rank611
private theorem cover611 : Cover (Triangular src611) 2313 2308 _root_.Research6970.Height2313.Physical.ends611 :=
  _root_.Research6970.Height2313.Physical.cover611

private abbrev src613 := _root_.Research6970.Height2313.Physical.src613
private theorem rank613 : P3_7_1.BankOK src613.bank := _root_.Research6970.Height2313.Physical.rank613
private theorem cover613 : Cover (Triangular src613) 2313 2308 _root_.Research6970.Height2313.Physical.ends613 :=
  _root_.Research6970.Height2313.Physical.cover613

private abbrev src614 := _root_.Research6970.Height2313.Physical.src614
private theorem rank614 : P3_7_1.BankOK src614.bank := _root_.Research6970.Height2313.Physical.rank614
private theorem cover614 : Cover (Triangular src614) 2313 2308 _root_.Research6970.Height2313.Physical.ends614 :=
  _root_.Research6970.Height2313.Physical.cover614

private abbrev src615 := _root_.Research6970.Height2313.Physical.src615
private theorem rank615 : P3_7_1.BankOK src615.bank := _root_.Research6970.Height2313.Physical.rank615
private theorem cover615 : Cover (Triangular src615) 2313 2308 _root_.Research6970.Height2313.Physical.ends615 :=
  _root_.Research6970.Height2313.Physical.cover615

private abbrev src616 := _root_.Research6970.Height2313.Physical.src616
private theorem rank616 : P3_7_1.BankOK src616.bank := _root_.Research6970.Height2313.Physical.rank616
private theorem cover616 : Cover (Triangular src616) 2313 2308 _root_.Research6970.Height2313.Physical.ends616 :=
  _root_.Research6970.Height2313.Physical.cover616

private abbrev src617 := _root_.Research6970.Height2313.Physical.src617
private theorem rank617 : P3_7_1.BankOK src617.bank := _root_.Research6970.Height2313.Physical.rank617
private theorem cover617 : Cover (Triangular src617) 2313 2308 _root_.Research6970.Height2313.Physical.ends617 :=
  _root_.Research6970.Height2313.Physical.cover617

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,3⟩
  bank f := ![src607.bank, src608.bank, src609.bank, src610.bank, src612.bank, src611.bank, src613.bank, src614.bank, src615.bank, src616.bank, src617.bank] f
  reserve f := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 27] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308364
  seedFloor := 3

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank607
    · exact rank608
    · exact rank609
    · exact rank610
    · exact rank612
    · exact rank611
    · exact rank613
    · exact rank614
    · exact rank615
    · exact rank616
    · exact rank617
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover607⟩
    · exact ⟨_, cover608⟩
    · exact ⟨_, cover609⟩
    · exact ⟨_, cover610⟩
    · exact ⟨_, cover612⟩
    · exact ⟨_, cover611⟩
    · exact ⟨_, cover613⟩
    · exact ⟨_, cover614⟩
    · exact ⟨_, cover615⟩
    · exact ⟨_, cover616⟩
    · exact ⟨_, cover617⟩

def price : TransferPrice := ⟨3, ![714709871655, 245361687083, 5904050040, 651353400], 36413616117674388⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.SeedThreeRescue

import ProximityPrize.SubmissionLower.Bundle6970_0d932b1d02cdb0ad
import ProximityPrize.SubmissionLower.Bundle6970_828b5b46b549b06d
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0


namespace Research6970.Height2308.Seed5Rescue

open _root_.Research6969.PhysicalWindow
open _root_.Lower6960
open Research6970.Height2313.Lower6960.Prefix6969Rescue

private abbrev src585 := _root_.Research6970.Height2313.Physical.src585
private theorem rank585 : P3_7_1.BankOK src585.bank := _root_.Research6970.Height2313.Physical.rank585
private theorem cover585 : Cover (Triangular src585) 2313 2308 _root_.Research6970.Height2313.Physical.ends585 :=
  _root_.Research6970.Height2313.Physical.cover585

private abbrev src586 := _root_.Research6970.Height2313.Physical.src586
private theorem rank586 : P3_7_1.BankOK src586.bank := _root_.Research6970.Height2313.Physical.rank586
private theorem cover586 : Cover (Triangular src586) 2313 2308 _root_.Research6970.Height2313.Physical.ends586 :=
  _root_.Research6970.Height2313.Physical.cover586

private abbrev src587 := _root_.Research6970.Height2313.Physical.src587
private theorem rank587 : P3_7_1.BankOK src587.bank := _root_.Research6970.Height2313.Physical.rank587
private theorem cover587 : Cover (Triangular src587) 2313 2308 _root_.Research6970.Height2313.Physical.ends587 :=
  _root_.Research6970.Height2313.Physical.cover587

private abbrev src588 := _root_.Research6970.Height2313.Physical.src588
private theorem rank588 : P3_7_1.BankOK src588.bank := _root_.Research6970.Height2313.Physical.rank588
private theorem cover588 : Cover (Triangular src588) 2313 2308 _root_.Research6970.Height2313.Physical.ends588 :=
  _root_.Research6970.Height2313.Physical.cover588

private abbrev src589 := _root_.Research6970.Height2313.Physical.src589
private theorem rank589 : P3_7_1.BankOK src589.bank := _root_.Research6970.Height2313.Physical.rank589
private theorem cover589 : Cover (Triangular src589) 2313 2308 _root_.Research6970.Height2313.Physical.ends589 :=
  _root_.Research6970.Height2313.Physical.cover589

private abbrev src590 := _root_.Research6970.Height2313.Physical.src590
private theorem rank590 : P3_7_1.BankOK src590.bank := _root_.Research6970.Height2313.Physical.rank590
private theorem cover590 : Cover (Triangular src590) 2313 2308 _root_.Research6970.Height2313.Physical.ends590 :=
  _root_.Research6970.Height2313.Physical.cover590

private abbrev src591 := _root_.Research6970.Height2313.Physical.src591
private theorem rank591 : P3_7_1.BankOK src591.bank := _root_.Research6970.Height2313.Physical.rank591
private theorem cover591 : Cover (Triangular src591) 2313 2308 _root_.Research6970.Height2313.Physical.ends591 :=
  _root_.Research6970.Height2313.Physical.cover591

private abbrev src592 := _root_.Research6970.Height2313.Physical.src592
private theorem rank592 : P3_7_1.BankOK src592.bank := _root_.Research6970.Height2313.Physical.rank592
private theorem cover592 : Cover (Triangular src592) 2313 2308 _root_.Research6970.Height2313.Physical.ends592 :=
  _root_.Research6970.Height2313.Physical.cover592

private abbrev src593 := _root_.Research6970.Height2313.Physical.src593
private theorem rank593 : P3_7_1.BankOK src593.bank := _root_.Research6970.Height2313.Physical.rank593
private theorem cover593 : Cover (Triangular src593) 2313 2308 _root_.Research6970.Height2313.Physical.ends593 :=
  _root_.Research6970.Height2313.Physical.cover593

private abbrev src594 := _root_.Research6970.Height2313.Physical.src594
private theorem rank594 : P3_7_1.BankOK src594.bank := _root_.Research6970.Height2313.Physical.rank594
private theorem cover594 : Cover (Triangular src594) 2313 2308 _root_.Research6970.Height2313.Physical.ends594 :=
  _root_.Research6970.Height2313.Physical.cover594

private abbrev src595 := _root_.Research6970.Height2313.Physical.src595
private theorem rank595 : P3_7_1.BankOK src595.bank := _root_.Research6970.Height2313.Physical.rank595
private theorem cover595 : Cover (Triangular src595) 2313 2308 _root_.Research6970.Height2313.Physical.ends595 :=
  _root_.Research6970.Height2313.Physical.cover595

def plan : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,5⟩
  bank f := ![src585.bank, src586.bank, src587.bank, src588.bank, src589.bank, src590.bank, src591.bank, src592.bank, src593.bank, src594.bank, src595.bank] f
  reserve f := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 32] f
  reserve_zero := by decide +kernel
  reserve_small := by intro f; fin_cases f <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro f; fin_cases f <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308319
  seedFloor := 5

theorem sources : plan.Sources 2308 2313 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; fin_cases f
    · exact rank585
    · exact rank586
    · exact rank587
    · exact rank588
    · exact rank589
    · exact rank590
    · exact rank591
    · exact rank592
    · exact rank593
    · exact rank594
    · exact rank595
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; fin_cases f <;> decide +kernel
  · intro f; unfold HelperSource.WidthGuard; fin_cases f <;> decide +kernel
  · intro f; fin_cases f
    · exact ⟨_, cover585⟩
    · exact ⟨_, cover586⟩
    · exact ⟨_, cover587⟩
    · exact ⟨_, cover588⟩
    · exact ⟨_, cover589⟩
    · exact ⟨_, cover590⟩
    · exact ⟨_, cover591⟩
    · exact ⟨_, cover592⟩
    · exact ⟨_, cover593⟩
    · exact ⟨_, cover594⟩
    · exact ⟨_, cover595⟩

def price : TransferPrice := ⟨5, ![1208361302288, 255457930912, 3785880728, 757188600], 32508988962298312⟩

theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Research6970.Height2308.Seed5Rescue

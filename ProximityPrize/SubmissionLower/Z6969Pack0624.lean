import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0618
import ProximityPrize.SubmissionLower.Z6969Pack0619
import ProximityPrize.SubmissionLower.Z6969Pack0620
import ProximityPrize.SubmissionLower.Z6969Pack0621
import ProximityPrize.SubmissionLower.Z6969Pack0622
import ProximityPrize.SubmissionLower.Z6969Pack0623

set_option Elab.async false

-- Source: Research6969.TransitionBankChecks20
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank360 (u : ℕ) : P3_7_1.BankOK (bank360 u) :=
  PackedRanks.PackedRanks360To362.rank360 u
theorem rank361 (u : ℕ) : P3_7_1.BankOK (bank361 u) :=
  PackedRanks.PackedRanks360To362.rank361 u
theorem rank362 (u : ℕ) : P3_7_1.BankOK (bank362 u) :=
  PackedRanks.PackedRanks360To362.rank362 u
theorem rank363 (u : ℕ) : P3_7_1.BankOK (bank363 u) :=
  PackedRanks.PackedRanks363To365.rank363 u
theorem rank364 (u : ℕ) : P3_7_1.BankOK (bank364 u) :=
  PackedRanks.PackedRanks363To365.rank364 u
theorem rank365 (u : ℕ) : P3_7_1.BankOK (bank365 u) :=
  PackedRanks.PackedRanks363To365.rank365 u
theorem rank366 (u : ℕ) : P3_7_1.BankOK (bank366 u) :=
  PackedRanks.PackedRanks366To368.rank366 u
theorem rank367 (u : ℕ) : P3_7_1.BankOK (bank367 u) :=
  PackedRanks.PackedRanks366To368.rank367 u
theorem rank368 (u : ℕ) : P3_7_1.BankOK (bank368 u) :=
  PackedRanks.PackedRanks366To368.rank368 u
theorem rank369 (u : ℕ) : P3_7_1.BankOK (bank369 u) :=
  PackedRanks.PackedRanks369To371.rank369 u
theorem rank370 (u : ℕ) : P3_7_1.BankOK (bank370 u) :=
  PackedRanks.PackedRanks369To371.rank370 u
theorem rank371 (u : ℕ) : P3_7_1.BankOK (bank371 u) :=
  PackedRanks.PackedRanks369To371.rank371 u
theorem rank372 (u : ℕ) : P3_7_1.BankOK (bank372 u) :=
  PackedRanks.PackedRanks372To374.rank372 u
theorem rank373 (u : ℕ) : P3_7_1.BankOK (bank373 u) :=
  PackedRanks.PackedRanks372To374.rank373 u
theorem rank374 (u : ℕ) : P3_7_1.BankOK (bank374 u) :=
  PackedRanks.PackedRanks372To374.rank374 u
theorem rank375 (u : ℕ) : P3_7_1.BankOK (bank375 u) :=
  PackedRanks.PackedRanks375To377.rank375 u
theorem rank376 (u : ℕ) : P3_7_1.BankOK (bank376 u) :=
  PackedRanks.PackedRanks375To377.rank376 u
theorem rank377 (u : ℕ) : P3_7_1.BankOK (bank377 u) :=
  PackedRanks.PackedRanks375To377.rank377 u
end Research6969.TransitionBanks

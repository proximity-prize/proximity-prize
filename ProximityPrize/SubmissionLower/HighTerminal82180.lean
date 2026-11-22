import ProximityPrize.SubmissionLower.HighBanks82180

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighTerminal82180

open Finset
open P3 (HighBand)
open P3_7 (Bank Test tested debit grades terminal threshold seedThreshold)
open P3_7_4 (BlockChecks)
open K1_14 (Shape shapeSum triangle slots)
open HighBanks82180 (adjusted count start)
open private slots_anti from ProximityPrize.SubmissionLower.UpperBranch6

private def weighted (c f : ℕ → ℕ) (g : ℕ) : ℕ :=
  (∑ a ∈ range g, (c a - c (a+1)) * f a) + c g * f g

private def width (A h : ℕ) (s : Shape) (q j a : ℕ) :=
  s.m*A + j - q*(131071-h) - 2*h*(j+a)

private def entry (A h : ℕ) (s : Shape) (E v q j : ℕ) :=
  weighted (fun a => slots s.U (a*v)) (width A h s q j) ((q-j)/E)

def gain (h : ℕ) (s : Shape) (E v : ℕ) :=
  shapeSum s (entry 179964 h s E v)

open private checks_at_grade from ProximityPrize.SubmissionLower.GoldBranch7N4

set_option quotPrecheck false
local notation "last!" l "," r => P3_7_4.Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => P3_7_4.Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => P3_7_4.certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

namespace H2274
local notation "S" u => (⟨6600,9172,1952,u⟩ : Shape)
local notation "N" => 8506872003288120
local notation "P" => 191486597252812
end H2274

namespace H2294
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 12667876648826196
local notation "P" => 327528160189452
end H2294

namespace H7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 52891447576
local notation "P" => 22832869
end H7773


end HighTerminal82180

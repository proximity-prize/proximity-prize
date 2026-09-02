/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Square-free spectral energy gate for the 1024-fibre attack

The prospective square-jet construction selects 136 of the 255 noncore
`mu_256` labels.  Its six moment coordinates and one cyclic product
coordinate form a key in a space of size `256 * p^6`.

Recent diagonal generalized-Paley graph formulas count ordered walks with
repetition.  The required object is their square-free analogue: the
coefficient of degree 136 in the product of the 255 character-valued linear
factors.  Parseval turns its total Fourier energy into the number of ordered
selector collisions.

This module formalizes the finite collision-energy implication and the exact
benchmark target.  It deliberately takes the collision-energy estimate as a
hypothesis; no currently proved character-sum theorem supplies that estimate.
-/

namespace ProximityPrize.SubmissionUpper.SquareFreeEnergyGate

open scoped BigOperators

/-- If the second moment of finite fibre sizes exceeds
`total * (target - 1)`, one fibre reaches `target`. -/
theorem exists_large_count_of_energy
    {Key : Type*} (keys : Finset Key) (count : Key → ℕ)
    (total target : ℕ) (htotal : 0 < total)
    (hmass : ∑ key ∈ keys, count key = total)
    (henergy : total * (target - 1) < ∑ key ∈ keys, (count key) ^ 2) :
    ∃ key ∈ keys, target ≤ count key := by
  classical
  by_contra hnone
  push Not at hnone
  have hpoint (key : Key) (hkey : key ∈ keys) :
      (count key) ^ 2 ≤ count key * (target - 1) := by
    have hcount : count key ≤ target - 1 :=
      Nat.le_sub_one_of_lt (hnone key hkey)
    simpa only [pow_two] using Nat.mul_le_mul_left (count key) hcount
  have hsum :
      ∑ key ∈ keys, (count key) ^ 2 ≤
        ∑ key ∈ keys, count key * (target - 1) := by
    exact Finset.sum_le_sum fun key hkey ↦ hpoint key hkey
  have hkeys : keys.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hmass
    simp only [Finset.sum_empty] at hmass
    omega
  obtain ⟨key, hkey⟩ := hkeys
  have _htarget : 0 < target := by
    have := hnone key hkey
    omega
  have hfactor :
      ∑ key ∈ keys, count key * (target - 1) = total * (target - 1) := by
    rw [← Finset.sum_mul, hmass]
  rw [hfactor] at hsum
  omega

def selectorCount : ℕ :=
  1642763237966455131089379983394824266573028270959430944304016753768099919875

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1
def keySpaceCardinality : ℕ := 256 * baseFieldCardinality ^ 6
def challengeThreshold : ℕ := 274980728111395088

/-- The scaled amount of nontrivial Fourier energy which, together with the
trivial character's `selectorCount^2`, reaches collision energy
`selectorCount * challengeThreshold`. -/
def nontrivialEnergyThreshold : ℕ :=
  selectorCount * (keySpaceCardinality * challengeThreshold - selectorCount)

/-- Hypergeometric mass of Johnson radii `55,...,72` for two 119-subsets of
a 255-element set. -/
def centralShellMass : ℕ :=
  1604393981273401333208095239916252893058440905420295119261055743422264080450

/-- Hypergeometric mass of the wider Johnson band `50,...,77`.  This band
retains almost all pairs and gives the sharpest convenient rational density
target in this module. -/
def wideCentralShellMass : ℕ :=
  1642096292370820721927822612803941981108479544435108111302321355662308556850

set_option maxRecDepth 1000000 in
theorem selector_count_receipt : selectorCount = Nat.choose 255 136 := by
  rw [Nat.choose_eq_fast_choose]
  decide

set_option maxRecDepth 1000000 in
theorem central_shell_mass_receipt :
    centralShellMass =
      ∑ r ∈ Finset.Icc 55 72, Nat.choose 119 r * Nat.choose 136 r := by
  decide

set_option maxRecDepth 1000000 in
theorem wide_central_shell_mass_receipt :
    wideCentralShellMass =
      ∑ r ∈ Finset.Icc 50 77, Nat.choose 119 r * Nat.choose 136 r := by
  decide

/-- Ordinary pigeonhole is just over four times too small, while five
average-sized fibres would suffice. -/
theorem mean_shortfall_receipt :
    4 * selectorCount < keySpaceCardinality * challengeThreshold ∧
      keySpaceCardinality * challengeThreshold < 5 * selectorCount := by
  norm_num [selectorCount, keySpaceCardinality, baseFieldCardinality,
    challengeThreshold]

/-- The required nontrivial spectral energy lies strictly between three and
four copies of the trivial Fourier energy. -/
theorem nontrivial_energy_window :
    3 * selectorCount ^ 2 < nontrivialEnergyThreshold ∧
      nontrivialEnergyThreshold < 4 * selectorCount ^ 2 := by
  norm_num [nontrivialEnergyThreshold, selectorCount, keySpaceCardinality,
    baseFieldCardinality, challengeThreshold]

/-- The central radius band carries more than `97.6643%` of the pair mass. -/
theorem central_shell_fraction_receipt :
    976643 * selectorCount < 1000000 * centralShellMass := by
  norm_num [selectorCount, centralShellMass]

/-- A `4.11`-times-uniform equal-key trade density on the central band is
enough for the sharp collision threshold. -/
theorem central_shell_density_receipt :
    100 * keySpaceCardinality * (challengeThreshold - 1) <
      411 * centralShellMass := by
  norm_num [keySpaceCardinality, baseFieldCardinality, challengeThreshold,
    centralShellMass]

/-- The wider band carries more than `99.9594%` of all selector pairs. -/
theorem wide_central_shell_fraction_receipt :
    999594 * selectorCount < 1000000 * wideCentralShellMass := by
  norm_num [selectorCount, wideCentralShellMass]

/-- A `4.012`-times-uniform equal-key trade density on radii `50,...,77`
already crosses the inclusive challenge threshold. -/
theorem wide_central_shell_density_receipt :
    1000 * keySpaceCardinality * (challengeThreshold - 1) <
      4012 * wideCentralShellMass := by
  norm_num [keySpaceCardinality, baseFieldCardinality, challengeThreshold,
    wideCentralShellMass]

/-- Consumer for a future balanced-trade count.  `bandContribution` is the
part of the collision energy from Johnson radii `55,...,72`; the scaled
density hypothesis is exactly what a shell count must prove. -/
theorem central_shell_certificate_suffices
    {Key : Type*} (keys : Finset Key) (count : Key → ℕ)
    (collisionEnergy bandContribution : ℕ)
    (hmass : ∑ key ∈ keys, count key = selectorCount)
    (hcollision : collisionEnergy = ∑ key ∈ keys, (count key) ^ 2)
    (hband : bandContribution ≤ collisionEnergy)
    (hdensity :
      411 * selectorCount * centralShellMass ≤
        100 * keySpaceCardinality * bandContribution) :
    ∃ key ∈ keys, challengeThreshold ≤ count key := by
  classical
  apply exists_large_count_of_energy keys count selectorCount challengeThreshold
    (by norm_num [selectorCount]) hmass
  rw [← hcollision]
  have hthreshold : selectorCount * (challengeThreshold - 1) <
      bandContribution := by
    norm_num [selectorCount, challengeThreshold, centralShellMass,
      keySpaceCardinality, baseFieldCardinality] at hdensity ⊢
    omega
  exact hthreshold.trans_le hband

/-- Consumer for a future balanced-trade count on the wider radius band.
The only construction-specific obligation is the scaled `hdensity` bound. -/
theorem wide_central_shell_certificate_suffices
    {Key : Type*} (keys : Finset Key) (count : Key → ℕ)
    (collisionEnergy bandContribution : ℕ)
    (hmass : ∑ key ∈ keys, count key = selectorCount)
    (hcollision : collisionEnergy = ∑ key ∈ keys, (count key) ^ 2)
    (hband : bandContribution ≤ collisionEnergy)
    (hdensity :
      4012 * selectorCount * wideCentralShellMass ≤
        1000 * keySpaceCardinality * bandContribution) :
    ∃ key ∈ keys, challengeThreshold ≤ count key := by
  classical
  apply exists_large_count_of_energy keys count selectorCount challengeThreshold
    (by norm_num [selectorCount]) hmass
  rw [← hcollision]
  have hthreshold : selectorCount * (challengeThreshold - 1) <
      bandContribution := by
    norm_num [selectorCount, challengeThreshold, wideCentralShellMass,
      keySpaceCardinality, baseFieldCardinality] at hdensity ⊢
    omega
  exact hthreshold.trans_le hband

/-- Exact integer form of the square-free Fourier/Parseval target. -/
theorem scaled_fourier_energy_suffices
    (scaledNontrivialEnergy collisionEnergy : ℕ)
    (hparseval : keySpaceCardinality * collisionEnergy =
      selectorCount ^ 2 + scaledNontrivialEnergy)
    (henergy : nontrivialEnergyThreshold ≤ scaledNontrivialEnergy) :
    selectorCount * challengeThreshold ≤ collisionEnergy := by
  norm_num [nontrivialEnergyThreshold, selectorCount, keySpaceCardinality,
    baseFieldCardinality, challengeThreshold] at hparseval henergy ⊢
  omega

end ProximityPrize.SubmissionUpper.SquareFreeEnergyGate

#print axioms ProximityPrize.SubmissionUpper.SquareFreeEnergyGate.exists_large_count_of_energy
#print axioms ProximityPrize.SubmissionUpper.SquareFreeEnergyGate.central_shell_certificate_suffices
#print axioms ProximityPrize.SubmissionUpper.SquareFreeEnergyGate.wide_central_shell_certificate_suffices
#print axioms ProximityPrize.SubmissionUpper.SquareFreeEnergyGate.scaled_fourier_energy_suffices

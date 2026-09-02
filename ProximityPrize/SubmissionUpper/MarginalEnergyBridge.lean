/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Marginal collision-energy bridge for the upper attack

Split the seven-coordinate selector key into one affine two-moment marginal
and the remaining four moments plus the cyclic product residue.  Cauchy in
each marginal fibre shows that collision energy can only fall by the number
of residual keys.  Consequently a `4.010`-times-uniform energy excess for any
one two-moment marginal is already sufficient for the full upper key.

This is a reduction theorem, not the missing arithmetic estimate.  Its value
is that it avoids any unjustified claim that two affine-moment zero fibres can
be multiplied or sequentially conditioned.
-/

namespace ProximityPrize.SubmissionUpper.MarginalEnergyBridge

open scoped BigOperators

/-- Fibrewise Cauchy: coarsening a two-coordinate table to its first
coordinate increases collision energy by at most the number of possible
second coordinates. -/
theorem marginal_energy_le_residual_card_mul_joint_energy
    {First Second : Type*} (firstKeys : Finset First)
    (secondKeys : Finset Second) (count : First → Second → ℕ) :
    ∑ first ∈ firstKeys, (∑ second ∈ secondKeys, count first second) ^ 2 ≤
      secondKeys.card *
        ∑ first ∈ firstKeys, ∑ second ∈ secondKeys,
          (count first second) ^ 2 := by
  calc
    ∑ first ∈ firstKeys, (∑ second ∈ secondKeys, count first second) ^ 2 ≤
        ∑ first ∈ firstKeys, secondKeys.card *
          ∑ second ∈ secondKeys, (count first second) ^ 2 := by
      exact Finset.sum_le_sum fun first _ ↦
        sq_sum_le_card_mul_sum_sq (s := secondKeys) (f := count first)
    _ = secondKeys.card *
        ∑ first ∈ firstKeys, ∑ second ∈ secondKeys,
          (count first second) ^ 2 := by
      simp only [Finset.mul_sum]

def selectorCount : ℕ :=
  1642763237966455131089379983394824266573028270959430944304016753768099919875

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1
def marginalKeySpaceCardinality : ℕ := baseFieldCardinality ^ 2
def residualKeySpaceCardinality : ℕ := 256 * baseFieldCardinality ^ 4
def fullKeySpaceCardinality : ℕ := 256 * baseFieldCardinality ^ 6
def challengeThreshold : ℕ := 274980728111395088

theorem key_space_factorization :
    fullKeySpaceCardinality =
      marginalKeySpaceCardinality * residualKeySpaceCardinality := by
  norm_num [fullKeySpaceCardinality, marginalKeySpaceCardinality,
    residualKeySpaceCardinality, baseFieldCardinality]

/-- The exact full-key deficit is strictly between `4.009` and `4.010` times
the uniform collision energy. -/
theorem exact_marginal_multiplier_window :
    4009 * selectorCount <
        1000 * fullKeySpaceCardinality * (challengeThreshold - 1) ∧
      1000 * fullKeySpaceCardinality * (challengeThreshold - 1) <
        4010 * selectorCount := by
  norm_num [selectorCount, fullKeySpaceCardinality, baseFieldCardinality,
    challengeThreshold]

/-- A `4.010`-times-uniform lower bound for one affine two-moment marginal,
together with fibrewise Cauchy, forces the full collision energy above the
inclusive challenge threshold. -/
theorem marginal_energy_excess_suffices
    (marginalEnergy jointEnergy : ℕ)
    (hcoarsen : marginalEnergy ≤ residualKeySpaceCardinality * jointEnergy)
    (henhance :
      4010 * selectorCount ^ 2 ≤
        1000 * marginalKeySpaceCardinality * marginalEnergy) :
    selectorCount * (challengeThreshold - 1) < jointEnergy := by
  have hscale :
      1000 * fullKeySpaceCardinality *
          (selectorCount * (challengeThreshold - 1)) <
        4010 * selectorCount ^ 2 := by
    norm_num [selectorCount, fullKeySpaceCardinality, baseFieldCardinality,
      challengeThreshold]
  have hfactor :
      marginalKeySpaceCardinality * residualKeySpaceCardinality =
        fullKeySpaceCardinality := by
    exact key_space_factorization.symm
  have hupper :
      1000 * marginalKeySpaceCardinality * marginalEnergy ≤
        1000 * fullKeySpaceCardinality * jointEnergy := by
    calc
      1000 * marginalKeySpaceCardinality * marginalEnergy ≤
          1000 * marginalKeySpaceCardinality *
            (residualKeySpaceCardinality * jointEnergy) := by
        exact Nat.mul_le_mul_left _ hcoarsen
      _ = 1000 * fullKeySpaceCardinality * jointEnergy := by
        rw [← hfactor]
        ring
  have hstrict :
      1000 * fullKeySpaceCardinality *
          (selectorCount * (challengeThreshold - 1)) <
        1000 * fullKeySpaceCardinality * jointEnergy :=
    hscale.trans_le (henhance.trans hupper)
  exact Nat.lt_of_mul_lt_mul_left hstrict

/-- Direct consumer combining the marginal bridge with the ordinary
second-moment pigeonhole principle. -/
theorem exists_large_count_of_marginal_energy
    {Key : Type*} (keys : Finset Key) (count : Key → ℕ)
    (marginalEnergy : ℕ)
    (hmass : ∑ key ∈ keys, count key = selectorCount)
    (hcoarsen : marginalEnergy ≤
      residualKeySpaceCardinality * ∑ key ∈ keys, (count key) ^ 2)
    (henhance :
      4010 * selectorCount ^ 2 ≤
        1000 * marginalKeySpaceCardinality * marginalEnergy) :
    ∃ key ∈ keys, challengeThreshold ≤ count key := by
  classical
  by_contra hnone
  push Not at hnone
  have hpoint (key : Key) (hkey : key ∈ keys) :
      (count key) ^ 2 ≤ count key * (challengeThreshold - 1) := by
    have hcount : count key ≤ challengeThreshold - 1 :=
      Nat.le_sub_one_of_lt (hnone key hkey)
    simpa only [pow_two] using Nat.mul_le_mul_left (count key) hcount
  have henergyUpper :
      ∑ key ∈ keys, (count key) ^ 2 ≤
        selectorCount * (challengeThreshold - 1) := by
    calc
      ∑ key ∈ keys, (count key) ^ 2 ≤
          ∑ key ∈ keys, count key * (challengeThreshold - 1) := by
        exact Finset.sum_le_sum fun key hkey ↦ hpoint key hkey
      _ = selectorCount * (challengeThreshold - 1) := by
        rw [← Finset.sum_mul, hmass]
  have hlower := marginal_energy_excess_suffices marginalEnergy
    (∑ key ∈ keys, (count key) ^ 2) hcoarsen henhance
  omega

end ProximityPrize.SubmissionUpper.MarginalEnergyBridge

#print axioms ProximityPrize.SubmissionUpper.MarginalEnergyBridge.marginal_energy_le_residual_card_mul_joint_energy
#print axioms ProximityPrize.SubmissionUpper.MarginalEnergyBridge.marginal_energy_excess_suffices
#print axioms ProximityPrize.SubmissionUpper.MarginalEnergyBridge.exists_large_count_of_marginal_energy

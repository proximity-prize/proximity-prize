/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Adaptive rate aggregation for upper collision profiles

The promoted lower `67.75` proof introduced a useful abstract mechanism:
partition an object into profiles, use the ordinary cap where its rate is
already good, and replace only the bad profiles by one of several sharper
caps.  If every chosen cap obeys a common rate against a conserved profile
mass, summing the local estimates gives one global bound.

This upper-only version contains no lower-track import or benchmark-specific
premise.  It is intended for collision/trade profiles indexed by radius,
period, defect, or carrier load.  A future shell census need only supply the
local replacement caps and their common-rate inequalities.
-/

namespace ProximityPrize.SubmissionUpper.AdaptiveRateAggregation

open scoped BigOperators

/-- A profile is bad when its ordinary cap exceeds the desired common rate. -/
def Bad {I : Type*} (totalCap bound : ℕ)
    (mass ordinary : I → ℕ) (i : I) : Prop :=
  bound * mass i < totalCap * ordinary i

/-- Sum any collection of local caps sharing one rate against conserved mass. -/
theorem aggregate_of_common_rate
    {I : Type*} [Fintype I]
    (mass count chosen : I → ℕ) (totalCap bound : ℕ)
    (hpositive : 0 < totalCap)
    (hmass : (∑ i, mass i) ≤ totalCap)
    (hcount : ∀ i, count i ≤ chosen i)
    (hrate : ∀ i, totalCap * chosen i ≤ bound * mass i) :
    (∑ i, count i) ≤ bound := by
  have hone (i : I) : totalCap * count i ≤ bound * mass i :=
    (Nat.mul_le_mul_left totalCap (hcount i)).trans (hrate i)
  have hscaled : totalCap * (∑ i, count i) ≤ totalCap * bound := by
    calc
      totalCap * (∑ i, count i) = ∑ i, totalCap * count i := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, bound * mass i := Finset.sum_le_sum fun i _ ↦ hone i
      _ = bound * (∑ i, mass i) := by rw [Finset.mul_sum]
      _ ≤ bound * totalCap := Nat.mul_le_mul_left bound hmass
      _ = totalCap * bound := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hpositive

/-- Adaptive version: retain an ordinary cap on good profiles and use a
replacement cap only on profiles where the ordinary rate fails. -/
theorem aggregate_of_rate_replacements
    {I : Type*} [Fintype I]
    (mass count ordinary replacement : I → ℕ)
    (totalCap bound : ℕ)
    (hpositive : 0 < totalCap)
    (hmass : (∑ i, mass i) ≤ totalCap)
    (hordinary : ∀ i, count i ≤ ordinary i)
    (hreplacement : ∀ i,
      Bad totalCap bound mass ordinary i → count i ≤ replacement i)
    (hreplacementRate : ∀ i,
      Bad totalCap bound mass ordinary i →
        totalCap * replacement i ≤ bound * mass i) :
    (∑ i, count i) ≤ bound := by
  classical
  apply aggregate_of_common_rate mass count
    (fun i ↦ if Bad totalCap bound mass ordinary i then replacement i else ordinary i)
    totalCap bound hpositive hmass
  · intro i
    by_cases hbad : Bad totalCap bound mass ordinary i
    · rw [if_pos hbad]
      exact hreplacement i hbad
    · rw [if_neg hbad]
      exact hordinary i
  · intro i
    by_cases hbad : Bad totalCap bound mass ordinary i
    · rw [if_pos hbad]
      exact hreplacementRate i hbad
    · rw [if_neg hbad]
      unfold Bad at hbad
      exact Nat.le_of_not_gt hbad

/-- Dual lower-rate summation used on the constructive side of the upper
attack.  Profile-dependent lower estimates can be combined without replacing
them by the weakest global estimate. -/
theorem aggregate_lower_rate
    {I : Type*} [Fintype I]
    (mass contribution : I → ℕ) (massFloor numerator denominator : ℕ)
    (hmass : massFloor ≤ ∑ i, mass i)
    (hrate : ∀ i, numerator * mass i ≤ denominator * contribution i) :
    numerator * massFloor ≤ denominator * ∑ i, contribution i := by
  calc
    numerator * massFloor ≤ numerator * (∑ i, mass i) :=
      Nat.mul_le_mul_left numerator hmass
    _ = ∑ i, numerator * mass i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, denominator * contribution i :=
      Finset.sum_le_sum fun i _ ↦ hrate i
    _ = denominator * ∑ i, contribution i := by rw [Finset.mul_sum]

end ProximityPrize.SubmissionUpper.AdaptiveRateAggregation

#print axioms ProximityPrize.SubmissionUpper.AdaptiveRateAggregation.aggregate_of_common_rate
#print axioms ProximityPrize.SubmissionUpper.AdaptiveRateAggregation.aggregate_of_rate_replacements
#print axioms ProximityPrize.SubmissionUpper.AdaptiveRateAggregation.aggregate_lower_rate

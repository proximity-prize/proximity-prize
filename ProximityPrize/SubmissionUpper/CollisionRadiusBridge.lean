/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Radius decomposition for square-free upper collisions

Two equal-size selectors differ by a disjoint signed trade.  If each side of
the trade has size `r`, the common part can be chosen in

`choose (n - 2 * r) (k - r)`

ways.  Consequently the collision energy at selector weight `k` is a
nonnegative linear combination of the balanced-trade counts.  At `n = 255`,
the coefficients for weights `136` and `119` agree exactly, so passing to
complements does not change the energy.

The second gate records the exact double-counting interface for restoring the
missing root of unity.  Translation invariance gives the two scaling
identities; after they are proved for a concrete trade relation, its full and
punctured likelihoods are identical.  No lower-track module is imported.
-/

namespace ProximityPrize.SubmissionUpper.CollisionRadiusBridge

open scoped BigOperators

/-- Number of common parts extending a disjoint radius-`r` trade to a pair of
`k`-subsets of an `n`-element universe. -/
def extensionWeight (n k r : ℕ) : ℕ := Nat.choose (n - 2 * r) (k - r)

/-- Complementary selector weights have the same extension coefficient. -/
theorem extension_weight_136_eq_119 (r : ℕ) (hr : r ≤ 119) :
    extensionWeight 255 136 r = extensionWeight 255 119 r := by
  have hle : 136 - r ≤ 255 - 2 * r := by omega
  have hsub : (255 - 2 * r) - (136 - r) = 119 - r := by omega
  calc
    extensionWeight 255 136 r = Nat.choose (255 - 2 * r) (136 - r) := rfl
    _ = Nat.choose (255 - 2 * r) ((255 - 2 * r) - (136 - r)) :=
      (Nat.choose_symm hle).symm
    _ = Nat.choose (255 - 2 * r) (119 - r) := by rw [hsub]
    _ = extensionWeight 255 119 r := rfl

/-- The formal collision-energy sums for complementary weights agree for
every sequence of balanced-trade counts. -/
theorem collision_energy_136_eq_119 (tradeCount : ℕ → ℕ) :
    (∑ r ∈ Finset.range 120, extensionWeight 255 136 r * tradeCount r) =
      ∑ r ∈ Finset.range 120, extensionWeight 255 119 r * tradeCount r := by
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r < 120 := Finset.mem_range.mp hr
  rw [extension_weight_136_eq_119 r (by omega)]

/-- Abstract double-counting gate for deleting one point from a transitive
`n`-point trade model.  The hypotheses say that both good trades and all
disjoint trades scale by the fraction `(n - 2r) / n`; the conclusion is exact
equality of their cross-multiplied likelihoods. -/
theorem puncture_preserves_likelihood
    (n support fullGood puncturedGood fullAll puncturedAll : ℕ)
    (hn : 0 < n)
    (hgood : n * puncturedGood = (n - support) * fullGood)
    (hall : n * puncturedAll = (n - support) * fullAll) :
    puncturedGood * fullAll = fullGood * puncturedAll := by
  have hleft : n * (puncturedGood * fullAll) =
      (n - support) * (fullGood * fullAll) := by
    calc
      n * (puncturedGood * fullAll) = (n * puncturedGood) * fullAll := by ring
      _ = ((n - support) * fullGood) * fullAll := by rw [hgood]
      _ = (n - support) * (fullGood * fullAll) := by ring
  have hright : n * (fullGood * puncturedAll) =
      (n - support) * (fullGood * fullAll) := by
    calc
      n * (fullGood * puncturedAll) = fullGood * (n * puncturedAll) := by ring
      _ = fullGood * ((n - support) * fullAll) := by rw [hall]
      _ = (n - support) * (fullGood * fullAll) := by ring
  exact Nat.eq_of_mul_eq_mul_left hn (hleft.trans hright.symm)

/-- A density lower bound proved in the full cyclic model transfers verbatim
to the punctured model.  This avoids paying for the missing root during the
Fourier or four-sheet calculation. -/
theorem punctured_density_of_full_density
    (n support fullGood puncturedGood fullAll puncturedAll scale : ℕ)
    (hn : 0 < n)
    (hgood : n * puncturedGood = (n - support) * fullGood)
    (hall : n * puncturedAll = (n - support) * fullAll)
    (hfull : scale * fullAll ≤ fullGood) :
    scale * puncturedAll ≤ puncturedGood := by
  have hcross := puncture_preserves_likelihood n support fullGood puncturedGood
    fullAll puncturedAll hn hgood hall
  by_cases hzero : fullAll = 0
  · have : puncturedAll = 0 := by
      have := hall
      simp [hzero] at this
      exact this.resolve_left (Nat.ne_of_gt hn)
    simp [this]
  · apply Nat.le_of_mul_le_mul_right _ (Nat.pos_of_ne_zero hzero)
    calc
      scale * puncturedAll * fullAll =
          puncturedAll * (scale * fullAll) := by ring
      _ ≤ puncturedAll * fullGood := Nat.mul_le_mul_left puncturedAll hfull
      _ = fullGood * puncturedAll := by ring
      _ = puncturedGood * fullAll := hcross.symm

end ProximityPrize.SubmissionUpper.CollisionRadiusBridge

#print axioms ProximityPrize.SubmissionUpper.CollisionRadiusBridge.collision_energy_136_eq_119
#print axioms ProximityPrize.SubmissionUpper.CollisionRadiusBridge.puncture_preserves_likelihood
#print axioms ProximityPrize.SubmissionUpper.CollisionRadiusBridge.punctured_density_of_full_density

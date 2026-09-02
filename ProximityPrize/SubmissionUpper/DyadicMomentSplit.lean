/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Dyadic splitting of upper selector moment relations

The square-free collision problem on `mu_256` can be restored from the
punctured label set and split along antipodal sheets.  Even moments see the
sum of the two sheets; odd moments see their difference.  Repeating the split
turns four consecutive Fourier checks on 128 sites into two ordinary
two-moment checks on 64 sites.

These identities are the precise algebraic interface between the upper
collision-energy attack and the affine two-moment objects developed on the
lower track.  This module is upper-only and proves just the identities.  It
does not import lower modules or assert the missing 81-state dictionary
count.
-/

namespace ProximityPrize.SubmissionUpper.DyadicMomentSplit

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Pair two sheets whose root labels differ by multiplication by `-1`. -/
theorem sum_pair_shift
    (n d : ℕ) (zeta : R) (hzeta : zeta ^ n = -1)
    (lower upper : Fin n → R) :
    ∑ j, (lower j * zeta ^ (d * j.val) +
        upper j * zeta ^ (d * (j.val + n))) =
      ∑ j, (lower j + (-1 : R) ^ d * upper j) * zeta ^ (d * j.val) := by
  apply Finset.sum_congr rfl
  intro j _hj
  have hdn : zeta ^ (d * n) = (-1 : R) ^ d := by
    rw [Nat.mul_comm d n, pow_mul, hzeta]
  have hshift : zeta ^ (d * (j.val + n)) =
      zeta ^ (d * j.val) * (-1 : R) ^ d := by
    simp only [Nat.mul_add, pow_add, hdn]
  rw [hshift]
  ring

/-- Even moments descend to the sum channel on the squared roots. -/
theorem sum_pair_shift_even
    (n e : ℕ) (zeta : R) (hzeta : zeta ^ n = -1)
    (lower upper : Fin n → R) :
    ∑ j, (lower j * zeta ^ ((2 * e) * j.val) +
        upper j * zeta ^ ((2 * e) * (j.val + n))) =
      ∑ j, (lower j + upper j) * (zeta ^ 2) ^ (e * j.val) := by
  rw [sum_pair_shift n (2 * e) zeta hzeta lower upper]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (-1 : R) ^ (2 * e) = 1 by simp [pow_mul]]
  simp only [one_mul]
  congr 1
  rw [← pow_mul]
  congr 1
  ring

/-- Odd moments descend to the difference channel with one residual root
factor. -/
theorem sum_pair_shift_odd
    (n e : ℕ) (zeta : R) (hzeta : zeta ^ n = -1)
    (lower upper : Fin n → R) :
    ∑ j, (lower j * zeta ^ ((2 * e + 1) * j.val) +
        upper j * zeta ^ ((2 * e + 1) * (j.val + n))) =
      ∑ j, (lower j - upper j) * zeta ^ j.val *
        (zeta ^ 2) ^ (e * j.val) := by
  rw [sum_pair_shift n (2 * e + 1) zeta hzeta lower upper]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (-1 : R) ^ (2 * e + 1) = -1 by simp [pow_succ, pow_mul]]
  rw [show lower j + -1 * upper j = lower j - upper j by ring]
  rw [← pow_mul]
  have hexponent : (2 * e + 1) * j.val = j.val + 2 * (e * j.val) := by ring
  rw [hexponent, pow_add]
  ring

section AffineChannels

variable {F : Type*} [Field F]

/-- The even sheet channel. -/
def plusChannel {n : ℕ} (lower upper : Fin n → F) (j : Fin n) : F :=
  lower j + upper j

/-- The odd sheet channel, normalized so exponents `-1` and `1` become
ordinary moments `0` and `1` on the squared roots. -/
def minusChannel {n : ℕ} (eta : F)
    (lower upper : Fin n → F) (j : Fin n) : F :=
  (lower j - upper j) * (eta⁻¹) ^ j.val

/-- Four consecutive checks `-1,0,1,2` split into two affine two-moment
checks.  This is the second dyadic split used by the 64-site dictionary. -/
theorem four_moments_to_two_affine_channels
    (n : ℕ) (eta : F) (heta : eta ≠ 0)
    (lower upper : Fin n → F)
    (hneg : (∑ j : Fin n, (lower j - upper j) * (eta⁻¹) ^ j.val) = 0)
    (hzero : (∑ j : Fin n, (lower j + upper j)) = 0)
    (hone : (∑ j : Fin n, (lower j - upper j) * eta ^ j.val) = 0)
    (htwo : (∑ j : Fin n, (lower j + upper j) * (eta ^ 2) ^ j.val) = 0) :
    ((∑ j : Fin n, plusChannel lower upper j) = 0) ∧
      ((∑ j : Fin n, plusChannel lower upper j * (eta ^ 2) ^ j.val) = 0) ∧
      ((∑ j : Fin n, minusChannel eta lower upper j) = 0) ∧
      ((∑ j : Fin n, minusChannel eta lower upper j * (eta ^ 2) ^ j.val) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [plusChannel] using hzero
  · simpa only [plusChannel] using htwo
  · simpa only [minusChannel] using hneg
  · rw [← hone]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [minusChannel]
    have hbase : eta⁻¹ * eta ^ 2 = eta := by
      field_simp
    calc
      (lower j - upper j) * (eta⁻¹) ^ j.val * (eta ^ 2) ^ j.val =
          (lower j - upper j) * ((eta⁻¹) ^ j.val * (eta ^ 2) ^ j.val) := by
            ring
      _ = (lower j - upper j) * (eta⁻¹ * eta ^ 2) ^ j.val := by
        rw [mul_pow]
      _ = (lower j - upper j) * eta ^ j.val := by rw [hbase]

end AffineChannels

end ProximityPrize.SubmissionUpper.DyadicMomentSplit

#print axioms ProximityPrize.SubmissionUpper.DyadicMomentSplit.sum_pair_shift
#print axioms ProximityPrize.SubmissionUpper.DyadicMomentSplit.four_moments_to_two_affine_channels

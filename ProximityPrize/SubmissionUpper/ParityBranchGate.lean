/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionUpper.SquareFreeEnergyGate

/-!
# Pure-parity exclusion for the four-sheet upper count

Two especially structured branches of a signed `mu_256` trade are

* the periodic branch `c (j + 128) = c j`, and
* the anti-periodic branch `c (j + 128) = -c j`.

For the first branch, one even Fourier equation reduces to a ternary relation
on `mu_128`; for the second, one odd equation does the same.  Exact packed
meet-in-the-middle certificates give the caps below after puncturing and
extension through the central radius band.  The computation intentionally
ignores the remaining field moments and the product equation, so the numbers
are upper bounds for the fully constrained branches.

Their sum is still below the mass needed by the 1024-fibre attack.  A closing
argument must therefore use configurations which genuinely mix the two
parity channels.  The independent standard-library audit checks the packed
dissociation assertions and regenerates both integers.
-/

namespace ProximityPrize.SubmissionUpper.ParityBranchGate

open ProximityPrize.SubmissionUpper.SquareFreeEnergyGate

/-- Padded cap for the entire period-128 branch, retaining only one even
field-moment equation. -/
def periodicBranchCap : ℕ :=
  234172479864737587901561624779110449785391089852707371970573392082401952019001295411845908922

/-- Padded cap for the entire anti-periodic branch, retaining only one odd
field-moment equation. -/
def antiPeriodicBranchCap : ℕ :=
  191940323036541379911590199895382505961164377412178988257959787770013974347115793895789690880

def pureParityBranchCap : ℕ := periodicBranchCap + antiPeriodicBranchCap

/-- Even after adding the two deliberately generous caps, pure parity
supplies less than `94.4%` of the collision mass required for an inclusive
challenge-size fibre. -/
theorem pure_parity_branch_cap_lt_944_per_mille :
    1000 * pureParityBranchCap <
      944 * (selectorCount * (challengeThreshold - 1)) := by
  norm_num [pureParityBranchCap, periodicBranchCap, antiPeriodicBranchCap,
    selectorCount, challengeThreshold]

theorem pure_parity_branch_cap_lt_required :
    pureParityBranchCap < selectorCount * (challengeThreshold - 1) := by
  have h := pure_parity_branch_cap_lt_944_per_mille
  norm_num [pureParityBranchCap, periodicBranchCap, antiPeriodicBranchCap,
    selectorCount, challengeThreshold] at h ⊢

/-- Consumer for a future decomposition theorem.  If the periodic and
anti-periodic pieces obey the exact caps and all three pieces close the energy
gate, the genuinely mixed-parity contribution is more than `5.6%` of the
required mass. -/
theorem mixed_parity_is_necessary
    (periodic antiPeriodic mixed : ℕ)
    (hperiodic : periodic ≤ periodicBranchCap)
    (hanti : antiPeriodic ≤ antiPeriodicBranchCap)
    (hclosure : selectorCount * (challengeThreshold - 1) ≤
      periodic + antiPeriodic + mixed) :
    56 * (selectorCount * (challengeThreshold - 1)) < 1000 * mixed := by
  have hpure : 1000 * (periodic + antiPeriodic) <
      944 * (selectorCount * (challengeThreshold - 1)) := by
    calc
      1000 * (periodic + antiPeriodic) ≤
          1000 * pureParityBranchCap := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add hperiodic hanti
      _ < 944 * (selectorCount * (challengeThreshold - 1)) :=
        pure_parity_branch_cap_lt_944_per_mille
  have hscaled : 1000 * (selectorCount * (challengeThreshold - 1)) ≤
      1000 * (periodic + antiPeriodic + mixed) :=
    Nat.mul_le_mul_left 1000 hclosure
  omega

end ProximityPrize.SubmissionUpper.ParityBranchGate

#print axioms ProximityPrize.SubmissionUpper.ParityBranchGate.pure_parity_branch_cap_lt_944_per_mille
#print axioms ProximityPrize.SubmissionUpper.ParityBranchGate.mixed_parity_is_necessary

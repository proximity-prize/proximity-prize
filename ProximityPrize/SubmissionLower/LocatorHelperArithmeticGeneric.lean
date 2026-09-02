/-
Dimension facts for the helper ("source-S") interpolation kernels used by the
generic multi-helper divisor-or-helper switch.

Provenance.  The generic multi-helper route is the public one from `jieyilong`
(PR #471); this file is the per-kernel arithmetic it consumes, and is the
several-kernel generalisation of `LocatorHelperArithmetic` /
`LocatorHelperGap` (single helper, `jieyilong` PR #451 and `i34-9` PR #456).
The cheap evaluation of `coefficientCount` goes through `LocatorKernelEval`,
adapted from the maintainer's `submission-helpers/KernelEval.lean` (PR #437);
the closed form of `localRankBound` goes through `LocatorRankClosed`, adapted
from `BitWonka` (PR #465).  The public `RCN100.coefficientCount` and
`RCN119.localRankBound` definitions are untouched: every big box is discharged
through one of those two equality lemmas and never by a plain `decide` on the
original definition.

A HELPER KERNEL IS NOT A SELECTED KERNEL.  These kernels do not enter the
joined kernel of `LocatorSelection` and are not fields of `SelectedPair`; they
are consumed only through `finrank_lower_bound` by the per-factor
divisor-or-helper dichotomy, exactly as `LocatorHelperGap` feeds
`LocatorHelperFactorSwitch.divisor_or_helper_count`.  Consequently their `L`
and `s` do NOT enter the residual pair box or the fixed support caps, and a
helper may be far larger than the ambient box.

CONSTANTS.  Every numeral below is one of the named constants in the first
section; a retune is a mechanical replacement of that section.  The placeholder
kernels are

  S1 = (m 355, L 350000, s 105)
  S2 = (m 500, L 1000000, s 150)
  S3 = (m 810, L 350000, s 243)

at `agreements = 181540` (row 6785).  For each kernel `S = (m, L, s)`:

  D       = m * agreements                      weighted degree
  y       = (D - 1) / w                         source `y` field
  cutoff  = y + 1                               minimal t with D ≤ w * t
  rank    = localRankBound m L s
  nullity = coefficientCount D w L s - n * rank the source `gap` field

The stage-capacity, shape and positivity lemmas are stated up to a named
`depth`; the placeholders 13 / 18 / 30 mirror the reference row, and the same
proofs go through unchanged for any depth up to 40 at these constants.
-/

import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.N5

namespace ProximityPrize.SubmissionLower.LocatorHelperArithmeticGeneric

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

/-! ### Row constants -/

/-- Ambient node count, `Fintype.card I`. -/
abbrev n : ℕ := 262144
/-- Selected-polynomial degree cap. -/
abbrev w : ℕ := 131071
/-- Agreement threshold of the row. -/
abbrev agreements : ℕ := 181540
/-- Stage step, `agreements - w + 1`. -/
abbrev delta : ℕ := 50470

/-! ### Helper kernel S1 -/

abbrev mS1 : ℕ := 355
abbrev LS1 : ℕ := 350000
abbrev sS1 : ℕ := 105
abbrev DS1 : ℕ := 64446700
abbrev yS1 : ℕ := 491
abbrev rankS1 : ℕ := 1789092129575
abbrev nullityS1 : ℕ := 3070668257066075
abbrev depthS1 : ℕ := 13

/-! ### Helper kernel S2 -/

abbrev mS2 : ℕ := 500
abbrev LS2 : ℕ := 1000000
abbrev sS2 : ℕ := 150
abbrev DS2 : ℕ := 90770000
abbrev yS2 : ℕ := 692
abbrev rankS2 : ℕ := 14383345717650
abbrev nullityS2 : ℕ := 27032429632837297
abbrev depthS2 : ℕ := 18

/-! ### Helper kernel S3 -/

abbrev mS3 : ℕ := 810
abbrev LS3 : ℕ := 350000
abbrev sS3 : ℕ := 243
abbrev DS3 : ℕ := 147047400
abbrev yS3 : ℕ := 1121
abbrev rankS3 : ℕ := 21307937367528
abbrev nullityS3 : ℕ := 41542667661965689
abbrev depthS3 : ℕ := 30

/-! ### Weighted degrees -/

theorem sourceS1_weighted : DS1 = mS1 * agreements := by decide
theorem sourceS2_weighted : DS2 = mS2 * agreements := by decide
theorem sourceS3_weighted : DS3 = mS3 * agreements := by decide

/-! ### Ranks, through the `LocatorRankClosed` closed form -/

theorem sourceS1_rank : localRankBound mS1 LS1 sS1 = rankS1 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS1 LS1 sS1 (by decide)]
  decide

theorem sourceS2_rank : localRankBound mS2 LS2 sS2 = rankS2 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS2 LS2 sS2 (by decide)]
  decide

theorem sourceS3_rank : localRankBound mS3 LS3 sS3 = rankS3 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS3 LS3 sS3 (by decide)]
  decide

/-! ### Nullities, through the `LocatorKernelEval` weighted cutoff -/

theorem sourceS1_nullity :
    coefficientCount DS1 w LS1 sS1 - n * localRankBound mS1 LS1 sS1 = nullityS1 := by
  rw [sourceS1_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS1 w LS1 sS1 (yS1 + 1) (by decide) (by decide)]
  decide

theorem sourceS2_nullity :
    coefficientCount DS2 w LS2 sS2 - n * localRankBound mS2 LS2 sS2 = nullityS2 := by
  rw [sourceS2_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS2 w LS2 sS2 (yS2 + 1) (by decide) (by decide)]
  decide

theorem sourceS3_nullity :
    coefficientCount DS3 w LS3 sS3 - n * localRankBound mS3 LS3 sS3 = nullityS3 := by
  rw [sourceS3_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS3 w LS3 sS3 (yS3 + 1) (by decide) (by decide)]
  decide

/-! ### Finrank lower bounds — the only way a helper kernel is consumed -/

private theorem kernel_finrank_lower
    (D L s m value : ℕ)
    (hvalue : coefficientCount D w L s - n * localRankBound m L s = value)
    (u0 u1 : I → K) :
    value ≤ Module.finrank K
      (ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = n := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    D w L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hvalue ▸ hlo'

theorem sourceS1_finrank_lower_bound (u0 u1 : I → K) :
    nullityS1 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS1 w LS1 sS1 mS1 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS1 LS1 sS1 mS1 nullityS1 sourceS1_nullity u0 u1

theorem sourceS2_finrank_lower_bound (u0 u1 : I → K) :
    nullityS2 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS2 w LS2 sS2 mS2 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS2 LS2 sS2 mS2 nullityS2 sourceS2_nullity u0 u1

theorem sourceS3_finrank_lower_bound (u0 u1 : I → K) :
    nullityS3 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS3 w LS3 sS3 mS3 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS3 LS3 sS3 mS3 nullityS3 sourceS3_nullity u0 u1

/-! ### Factorial casts for the stage tower

The deep helper arms take derivatives up to the route depth, so the stage
factorials must be nonzero in the field.  The bound is the characteristic, so
any depth this certificate could use is covered. -/

theorem factorial_cast_ne_zero
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j < 2130706433) : (j.factorial : E) ≠ 0 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply mul_ne_zero
      · intro hz
        have hdvd : 2130706433 ∣ j + 1 :=
          (CharP.cast_eq_zero_iff E 2130706433 (j + 1)).mp hz
        exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
      · exact ih (by omega)

/-- The shape the reference port uses; a corollary of `factorial_cast_ne_zero`. -/
theorem factorial_cast_ne_zero_of_le_thirty
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j ≤ 30) : (j.factorial : E) ≠ 0 :=
  factorial_cast_ne_zero j (by omega)

/-! ### Stage capacity, positivity and shape -/

theorem sourceS1_stage_capacity (j : ℕ) (hj : j ≤ depthS1) :
    DS1 - j * delta = (mS1 - j) * agreements + j * (w - 1) := by
  unfold DS1 delta mS1 agreements w depthS1 at *
  omega

theorem sourceS2_stage_capacity (j : ℕ) (hj : j ≤ depthS2) :
    DS2 - j * delta = (mS2 - j) * agreements + j * (w - 1) := by
  unfold DS2 delta mS2 agreements w depthS2 at *
  omega

theorem sourceS3_stage_capacity (j : ℕ) (hj : j ≤ depthS3) :
    DS3 - j * delta = (mS3 - j) * agreements + j * (w - 1) := by
  unfold DS3 delta mS3 agreements w depthS3 at *
  omega

theorem sourceS1_low_positive (j : ℕ) (hj : j ≤ depthS1) : 0 < DS1 - j * delta := by
  unfold DS1 delta depthS1 at *
  omega

theorem sourceS2_low_positive (j : ℕ) (hj : j ≤ depthS2) : 0 < DS2 - j * delta := by
  unfold DS2 delta depthS2 at *
  omega

theorem sourceS3_low_positive (j : ℕ) (hj : j ≤ depthS3) : 0 < DS3 - j * delta := by
  unfold DS3 delta depthS3 at *
  omega

theorem sourceS1_shape : DS1 + sS1 ≤ w * (yS1 + 1) := by decide
theorem sourceS2_shape : DS2 + sS2 ≤ w * (yS2 + 1) := by decide
theorem sourceS3_shape : DS3 + sS3 ≤ w * (yS3 + 1) := by decide

end

end ProximityPrize.SubmissionLower.LocatorHelperArithmeticGeneric

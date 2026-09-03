/-
Dimension facts for every interpolation kernel consumed as a route source by
the generic divisor-or-helper switch, row 6786 (agreements 181530).

Provenance.  The generic multi-helper route is the public one from `jieyilong`
(PR #471, 67.84) with the per-source arithmetic pattern of that port; the cheap
evaluation of `coefficientCount` goes through `LocatorKernelEval` (maintainer's
`submission-helpers/KernelEval.lean`, PR #437) and the closed form of
`localRankBound` through `LocatorRankClosed` (`BitWonka`, PR #465).

A SOURCE KERNEL IS NOT A SELECTED KERNEL.  None of these kernels enters the
joined kernel of `LocatorSelection`; each is consumed only through its finrank
lower bound by the per-factor divisor-or-helper dichotomy, so its `L` and `s`
never enter the residual pair box or the fixed support caps.

Sources (`S = (m, L, s)`, `D = m * agreements`, `y = (D - 1) / w`,
`nullity = coefficientCount D w L s - n * localRankBound m L s`):
  A   = (75, 130000, 22)   depth 1     Aux = (75, 130000, 23)   depth 1
  C   = (400, 130000, 120) depth 14    S1  = (355, 350000, 105) depth 13
  S2  = (500, 1000000, 150) depth 18   S3  = (810, 350000, 243) depth 30
  S4  = (810, 2000000, 243) depth 33   S5  = (400, 1000000, 120) depth 17
  S6  = (560, 20000, 170)  depth 10    S7  = (570, 30000, 170)  depth 12
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

abbrev n : ℕ := 262144
abbrev w : ℕ := 131071
abbrev agreements : ℕ := 181530
abbrev delta : ℕ := 50460

/-! ### Source kernel A = (75, 130000, 22) -/

abbrev mA : ℕ := 75
abbrev LA : ℕ := 130000
abbrev sA : ℕ := 22
abbrev DA : ℕ := 13614750
abbrev yA : ℕ := 103
abbrev rankA : ℕ := 6546495014
abbrev nullityA : ℕ := 351572585294
abbrev depthA : ℕ := 1

/-! ### Source kernel Aux = (75, 130000, 23) -/

abbrev mAux : ℕ := 75
abbrev LAux : ℕ := 130000
abbrev sAux : ℕ := 23
abbrev DAux : ℕ := 13614750
abbrev yAux : ℕ := 103
abbrev rankAux : ℕ := 6761440848
abbrev nullityAux : ℕ := 396080340478
abbrev depthAux : ℕ := 1

/-! ### Source kernel C = (400, 130000, 120) -/

abbrev mC : ℕ := 400
abbrev LC : ℕ := 130000
abbrev sC : ℕ := 120
abbrev DC : ℕ := 72612000
abbrev yC : ℕ := 553
abbrev rankC : ℕ := 958541142020
abbrev nullityC : ℕ := 1622595225055178
abbrev depthC : ℕ := 14

/-! ### Source kernel S1 = (355, 350000, 105) -/

abbrev mS1 : ℕ := 355
abbrev LS1 : ℕ := 350000
abbrev sS1 : ℕ := 105
abbrev DS1 : ℕ := 64443150
abbrev yS1 : ℕ := 491
abbrev rankS1 : ℕ := 1789092129575
abbrev nullityS1 : ℕ := 3012828511088025
abbrev depthS1 : ℕ := 13

/-! ### Source kernel S2 = (500, 1000000, 150) -/

abbrev mS2 : ℕ := 500
abbrev LS2 : ℕ := 1000000
abbrev sS2 : ℕ := 150
abbrev DS2 : ℕ := 90765000
abbrev yS2 : ℕ := 692
abbrev rankS2 : ℕ := 14383345717650
abbrev nullityS2 : ℕ := 26566017386262297
abbrev depthS2 : ℕ := 18

/-! ### Source kernel S3 = (810, 350000, 243) -/

abbrev mS3 : ℕ := 810
abbrev LS3 : ℕ := 350000
abbrev sS3 : ℕ := 243
abbrev DS3 : ℕ := 147039300
abbrev yS3 : ℕ := 1121
abbrev rankS3 : ℕ := 21307937367528
abbrev nullityS3 : ℕ := 40851803364289489
abbrev depthS3 : ℕ := 30

/-! ### Source kernel S4 = (810, 2000000, 243) -/

abbrev mS4 : ℕ := 810
abbrev LS4 : ℕ := 2000000
abbrev sS4 : ℕ := 243
abbrev DS4 : ℕ := 147039300
abbrev yS4 : ℕ := 1121
abbrev rankS4 : ℕ := 121862722467528
abbrev nullityS4 : ℕ := 240339549990589489
abbrev depthS4 : ℕ := 33

/-! ### Source kernel S5 = (400, 1000000, 120) -/

abbrev mS5 : ℕ := 400
abbrev LS5 : ℕ := 1000000
abbrev sS5 : ℕ := 120
abbrev DS5 : ℕ := 72612000
abbrev yS5 : ℕ := 553
abbrev rankS5 : ℕ := 7382116542020
abbrev nullityS5 : ℕ := 13064567220685178
abbrev depthS5 : ℕ := 17

/-! ### Source kernel S6 = (560, 20000, 170) -/

abbrev mS6 : ℕ := 560
abbrev LS6 : ℕ := 20000
abbrev sS6 : ℕ := 170
abbrev DS6 : ℕ := 101656800
abbrev yS6 : ℕ := 775
abbrev rankS6 : ℕ := 402402095160
abbrev nullityS6 : ℕ := 440799821601495
abbrev depthS6 : ℕ := 10

/-! ### Source kernel S7 = (570, 30000, 170) -/

abbrev mS7 : ℕ := 570
abbrev LS7 : ℕ := 30000
abbrev sS7 : ℕ := 170
abbrev DS7 : ℕ := 103472100
abbrev yS7 : ℕ := 789
abbrev rankS7 : ℕ := 630511727250
abbrev nullityS7 : ℕ := 845803391069760
abbrev depthS7 : ℕ := 12

/-! ### Weighted degrees -/

theorem sourceA_weighted : DA = mA * agreements := by decide
theorem sourceAux_weighted : DAux = mAux * agreements := by decide
theorem sourceC_weighted : DC = mC * agreements := by decide
theorem sourceS1_weighted : DS1 = mS1 * agreements := by decide
theorem sourceS2_weighted : DS2 = mS2 * agreements := by decide
theorem sourceS3_weighted : DS3 = mS3 * agreements := by decide
theorem sourceS4_weighted : DS4 = mS4 * agreements := by decide
theorem sourceS5_weighted : DS5 = mS5 * agreements := by decide
theorem sourceS6_weighted : DS6 = mS6 * agreements := by decide
theorem sourceS7_weighted : DS7 = mS7 * agreements := by decide

/-! ### Ranks, through the `LocatorRankClosed` closed form -/

theorem sourceA_rank : localRankBound mA LA sA = rankA := by
  rw [LocatorRankClosed.localRankBound_eq_fast mA LA sA (by decide)]
  decide

theorem sourceAux_rank : localRankBound mAux LAux sAux = rankAux := by
  rw [LocatorRankClosed.localRankBound_eq_fast mAux LAux sAux (by decide)]
  decide

theorem sourceC_rank : localRankBound mC LC sC = rankC := by
  rw [LocatorRankClosed.localRankBound_eq_fast mC LC sC (by decide)]
  decide

theorem sourceS1_rank : localRankBound mS1 LS1 sS1 = rankS1 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS1 LS1 sS1 (by decide)]
  decide

theorem sourceS2_rank : localRankBound mS2 LS2 sS2 = rankS2 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS2 LS2 sS2 (by decide)]
  decide

theorem sourceS3_rank : localRankBound mS3 LS3 sS3 = rankS3 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS3 LS3 sS3 (by decide)]
  decide

theorem sourceS4_rank : localRankBound mS4 LS4 sS4 = rankS4 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS4 LS4 sS4 (by decide)]
  decide

theorem sourceS5_rank : localRankBound mS5 LS5 sS5 = rankS5 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS5 LS5 sS5 (by decide)]
  decide

theorem sourceS6_rank : localRankBound mS6 LS6 sS6 = rankS6 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS6 LS6 sS6 (by decide)]
  decide

theorem sourceS7_rank : localRankBound mS7 LS7 sS7 = rankS7 := by
  rw [LocatorRankClosed.localRankBound_eq_fast mS7 LS7 sS7 (by decide)]
  decide

/-! ### Nullities, through the `LocatorKernelEval` weighted cutoff -/

theorem sourceA_nullity :
    coefficientCount DA w LA sA - n * localRankBound mA LA sA = nullityA := by
  rw [sourceA_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DA w LA sA (yA + 1) (by decide) (by decide)]
  decide

theorem sourceAux_nullity :
    coefficientCount DAux w LAux sAux - n * localRankBound mAux LAux sAux = nullityAux := by
  rw [sourceAux_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DAux w LAux sAux (yAux + 1) (by decide) (by decide)]
  decide

theorem sourceC_nullity :
    coefficientCount DC w LC sC - n * localRankBound mC LC sC = nullityC := by
  rw [sourceC_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DC w LC sC (yC + 1) (by decide) (by decide)]
  decide

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

theorem sourceS4_nullity :
    coefficientCount DS4 w LS4 sS4 - n * localRankBound mS4 LS4 sS4 = nullityS4 := by
  rw [sourceS4_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS4 w LS4 sS4 (yS4 + 1) (by decide) (by decide)]
  decide

theorem sourceS5_nullity :
    coefficientCount DS5 w LS5 sS5 - n * localRankBound mS5 LS5 sS5 = nullityS5 := by
  rw [sourceS5_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS5 w LS5 sS5 (yS5 + 1) (by decide) (by decide)]
  decide

theorem sourceS6_nullity :
    coefficientCount DS6 w LS6 sS6 - n * localRankBound mS6 LS6 sS6 = nullityS6 := by
  rw [sourceS6_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS6 w LS6 sS6 (yS6 + 1) (by decide) (by decide)]
  decide

theorem sourceS7_nullity :
    coefficientCount DS7 w LS7 sS7 - n * localRankBound mS7 LS7 sS7 = nullityS7 := by
  rw [sourceS7_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    DS7 w LS7 sS7 (yS7 + 1) (by decide) (by decide)]
  decide

/-! ### Finrank lower bounds — the only way a source kernel is consumed -/

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

theorem sourceA_finrank_lower_bound (u0 u1 : I → K) :
    nullityA ≤ Module.finrank K
      (ConstraintKernel (K := K) DA w LA sA mA IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DA LA sA mA nullityA sourceA_nullity u0 u1

theorem sourceAux_finrank_lower_bound (u0 u1 : I → K) :
    nullityAux ≤ Module.finrank K
      (ConstraintKernel (K := K) DAux w LAux sAux mAux IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DAux LAux sAux mAux nullityAux sourceAux_nullity u0 u1

theorem sourceC_finrank_lower_bound (u0 u1 : I → K) :
    nullityC ≤ Module.finrank K
      (ConstraintKernel (K := K) DC w LC sC mC IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DC LC sC mC nullityC sourceC_nullity u0 u1

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

theorem sourceS4_finrank_lower_bound (u0 u1 : I → K) :
    nullityS4 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS4 w LS4 sS4 mS4 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS4 LS4 sS4 mS4 nullityS4 sourceS4_nullity u0 u1

theorem sourceS5_finrank_lower_bound (u0 u1 : I → K) :
    nullityS5 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS5 w LS5 sS5 mS5 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS5 LS5 sS5 mS5 nullityS5 sourceS5_nullity u0 u1

theorem sourceS6_finrank_lower_bound (u0 u1 : I → K) :
    nullityS6 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS6 w LS6 sS6 mS6 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS6 LS6 sS6 mS6 nullityS6 sourceS6_nullity u0 u1

theorem sourceS7_finrank_lower_bound (u0 u1 : I → K) :
    nullityS7 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS7 w LS7 sS7 mS7 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower DS7 LS7 sS7 mS7 nullityS7 sourceS7_nullity u0 u1

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

/-- The shape the reference port uses; a corollary of `factorial_cast_ne_zero`.
The name is historical: the bound is the grid's `depthCap`, here `34`. -/
theorem factorial_cast_ne_zero_of_le_thirty
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j ≤ 34) : (j.factorial : E) ≠ 0 :=
  factorial_cast_ne_zero j (by omega)

/-! ### Stage capacity, positivity and shape

The capacity identity holds with equality for every `j ≤ m`, because
`agreements - (w - 1) = delta`; it is stated up to the source's depth. -/

theorem sourceA_stage_capacity (j : ℕ) (hj : j ≤ depthA) :
    DA - j * delta = (mA - j) * agreements + j * (w - 1) := by
  unfold DA delta mA agreements w depthA at *
  omega

theorem sourceA_low_positive (j : ℕ) (hj : j ≤ depthA) : 0 < DA - j * delta := by
  unfold DA delta depthA at *
  omega

theorem sourceA_shape : DA + sA ≤ w * (yA + 1) := by decide

theorem sourceAux_stage_capacity (j : ℕ) (hj : j ≤ depthAux) :
    DAux - j * delta = (mAux - j) * agreements + j * (w - 1) := by
  unfold DAux delta mAux agreements w depthAux at *
  omega

theorem sourceAux_low_positive (j : ℕ) (hj : j ≤ depthAux) : 0 < DAux - j * delta := by
  unfold DAux delta depthAux at *
  omega

theorem sourceAux_shape : DAux + sAux ≤ w * (yAux + 1) := by decide

theorem sourceC_stage_capacity (j : ℕ) (hj : j ≤ depthC) :
    DC - j * delta = (mC - j) * agreements + j * (w - 1) := by
  unfold DC delta mC agreements w depthC at *
  omega

theorem sourceC_low_positive (j : ℕ) (hj : j ≤ depthC) : 0 < DC - j * delta := by
  unfold DC delta depthC at *
  omega

theorem sourceC_shape : DC + sC ≤ w * (yC + 1) := by decide

theorem sourceS1_stage_capacity (j : ℕ) (hj : j ≤ depthS1) :
    DS1 - j * delta = (mS1 - j) * agreements + j * (w - 1) := by
  unfold DS1 delta mS1 agreements w depthS1 at *
  omega

theorem sourceS1_low_positive (j : ℕ) (hj : j ≤ depthS1) : 0 < DS1 - j * delta := by
  unfold DS1 delta depthS1 at *
  omega

theorem sourceS1_shape : DS1 + sS1 ≤ w * (yS1 + 1) := by decide

theorem sourceS2_stage_capacity (j : ℕ) (hj : j ≤ depthS2) :
    DS2 - j * delta = (mS2 - j) * agreements + j * (w - 1) := by
  unfold DS2 delta mS2 agreements w depthS2 at *
  omega

theorem sourceS2_low_positive (j : ℕ) (hj : j ≤ depthS2) : 0 < DS2 - j * delta := by
  unfold DS2 delta depthS2 at *
  omega

theorem sourceS2_shape : DS2 + sS2 ≤ w * (yS2 + 1) := by decide

theorem sourceS3_stage_capacity (j : ℕ) (hj : j ≤ depthS3) :
    DS3 - j * delta = (mS3 - j) * agreements + j * (w - 1) := by
  unfold DS3 delta mS3 agreements w depthS3 at *
  omega

theorem sourceS3_low_positive (j : ℕ) (hj : j ≤ depthS3) : 0 < DS3 - j * delta := by
  unfold DS3 delta depthS3 at *
  omega

theorem sourceS3_shape : DS3 + sS3 ≤ w * (yS3 + 1) := by decide

theorem sourceS4_stage_capacity (j : ℕ) (hj : j ≤ depthS4) :
    DS4 - j * delta = (mS4 - j) * agreements + j * (w - 1) := by
  unfold DS4 delta mS4 agreements w depthS4 at *
  omega

theorem sourceS4_low_positive (j : ℕ) (hj : j ≤ depthS4) : 0 < DS4 - j * delta := by
  unfold DS4 delta depthS4 at *
  omega

theorem sourceS4_shape : DS4 + sS4 ≤ w * (yS4 + 1) := by decide

theorem sourceS5_stage_capacity (j : ℕ) (hj : j ≤ depthS5) :
    DS5 - j * delta = (mS5 - j) * agreements + j * (w - 1) := by
  unfold DS5 delta mS5 agreements w depthS5 at *
  omega

theorem sourceS5_low_positive (j : ℕ) (hj : j ≤ depthS5) : 0 < DS5 - j * delta := by
  unfold DS5 delta depthS5 at *
  omega

theorem sourceS5_shape : DS5 + sS5 ≤ w * (yS5 + 1) := by decide

theorem sourceS6_stage_capacity (j : ℕ) (hj : j ≤ depthS6) :
    DS6 - j * delta = (mS6 - j) * agreements + j * (w - 1) := by
  unfold DS6 delta mS6 agreements w depthS6 at *
  omega

theorem sourceS6_low_positive (j : ℕ) (hj : j ≤ depthS6) : 0 < DS6 - j * delta := by
  unfold DS6 delta depthS6 at *
  omega

theorem sourceS6_shape : DS6 + sS6 ≤ w * (yS6 + 1) := by decide

theorem sourceS7_stage_capacity (j : ℕ) (hj : j ≤ depthS7) :
    DS7 - j * delta = (mS7 - j) * agreements + j * (w - 1) := by
  unfold DS7 delta mS7 agreements w depthS7 at *
  omega

theorem sourceS7_low_positive (j : ℕ) (hj : j ≤ depthS7) : 0 < DS7 - j * delta := by
  unfold DS7 delta depthS7 at *
  omega

theorem sourceS7_shape : DS7 + sS7 ≤ w * (yS7 + 1) := by decide

end

end ProximityPrize.SubmissionLower.LocatorHelperArithmeticGeneric

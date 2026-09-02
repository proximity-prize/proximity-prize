/-
Dimension facts for every route source of row 6787 (agreements 181520): the A, Aux and C kernels
and the helper kernels. Ranks/nullities come from the per-source modules `LocatorSourceKernel*`
(closed-form rank via `LocatorRankClosed`, cutoff count via `LocatorKernelEval`, row-chunked for the
long kernels). A source kernel is not a selected kernel: it is consumed only through its finrank
lower bound by the per-factor divisor-or-helper dichotomy.
-/
import ProximityPrize.SubmissionLower.LocatorSourceKernelA
import ProximityPrize.SubmissionLower.LocatorSourceKernelAux
import ProximityPrize.SubmissionLower.LocatorSourceKernelC
import ProximityPrize.SubmissionLower.LocatorSourceKernelS2
import ProximityPrize.SubmissionLower.LocatorSourceKernelS3
import ProximityPrize.SubmissionLower.LocatorSourceKernelH3X
import ProximityPrize.SubmissionLower.LocatorSourceKernelH4
import ProximityPrize.SubmissionLower.LocatorSourceKernelT10k
import ProximityPrize.SubmissionLower.LocatorSourceKernelT15k
import ProximityPrize.SubmissionLower.LocatorSourceKernelT20k
import ProximityPrize.SubmissionLower.LocatorSourceKernelT30k
import ProximityPrize.SubmissionLower.LocatorSourceKernelL1
import ProximityPrize.SubmissionLower.LocatorSourceKernelL2
import ProximityPrize.SubmissionLower.LocatorSourceKernelL3
import ProximityPrize.SubmissionLower.LocatorSourceKernelL4
import ProximityPrize.SubmissionLower.LocatorSourceKernelL5
import ProximityPrize.SubmissionLower.LocatorSourceKernelL6
import ProximityPrize.SubmissionLower.LocatorSourceKernelM1
import ProximityPrize.SubmissionLower.LocatorSourceKernelM3
import ProximityPrize.SubmissionLower.LocatorSourceKernelN1
import ProximityPrize.SubmissionLower.LocatorSourceKernelN3
import ProximityPrize.SubmissionLower.LocatorSourceKernelN4
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
abbrev agreements : ℕ := 181520
abbrev delta : ℕ := 50450

/-! ### Source kernel A = (76, 130000, 22) -/

abbrev mA : ℕ := 76
abbrev LA : ℕ := 130000
abbrev sA : ℕ := 22
abbrev DA : ℕ := 13795520
abbrev yA : ℕ := 105
abbrev rankA : ℕ := 6740780706
abbrev nullityA : ℕ := 255124945551
abbrev depthA : ℕ := 1

/-! ### Source kernel Aux = (76, 130000, 23) -/

abbrev mAux : ℕ := 76
abbrev LAux : ℕ := 130000
abbrev sAux : ℕ := 23
abbrev DAux : ℕ := 13795520
abbrev yAux : ℕ := 105
abbrev rankAux : ℕ := 6962613720
abbrev nullityAux : ℕ := 422421820346
abbrev depthAux : ℕ := 1

/-! ### Source kernel C = (400, 130000, 120) -/

abbrev mC : ℕ := 400
abbrev LC : ℕ := 130000
abbrev sC : ℕ := 120
abbrev DC : ℕ := 72608000
abbrev yC : ℕ := 553
abbrev rankC : ℕ := 958541142020
abbrev nullityC : ℕ := 1591585493643178
abbrev depthC : ℕ := 14

/-! ### Source kernel S2 = (500, 1000000, 150) -/

abbrev mS2 : ℕ := 500
abbrev LS2 : ℕ := 1000000
abbrev sS2 : ℕ := 150
abbrev DS2 : ℕ := 90760000
abbrev yS2 : ℕ := 692
abbrev rankS2 : ℕ := 14383345717650
abbrev nullityS2 : ℕ := 26099605139687297
abbrev depthS2 : ℕ := 18

/-! ### Source kernel S3 = (810, 350000, 243) -/

abbrev mS3 : ℕ := 810
abbrev LS3 : ℕ := 350000
abbrev sS3 : ℕ := 243
abbrev DS3 : ℕ := 147031200
abbrev yS3 : ℕ := 1121
abbrev rankS3 : ℕ := 21307937367528
abbrev nullityS3 : ℕ := 40160939066613289
abbrev depthS3 : ℕ := 30

/-! ### Source kernel H3X = (810, 2000000, 243) -/

abbrev mH3X : ℕ := 810
abbrev LH3X : ℕ := 2000000
abbrev sH3X : ℕ := 243
abbrev DH3X : ℕ := 147031200
abbrev yH3X : ℕ := 1121
abbrev rankH3X : ℕ := 121862722467528
abbrev nullityH3X : ℕ := 236385995162913289
abbrev depthH3X : ℕ := 32

/-! ### Source kernel H4 = (1000, 2000000, 300) -/

abbrev mH4 : ℕ := 1000
abbrev LH4 : ℕ := 2000000
abbrev sH4 : ℕ := 300
abbrev DH4 : ℕ := 181520000
abbrev yH4 : ℕ := 1384
abbrev rankH4 : ℕ := 229040327786550
abbrev nullityH4 : ℕ := 452270055375521215
abbrev depthH4 : ℕ := 36

/-! ### Source kernel T10k = (540, 10000, 170) -/

abbrev mT10k : ℕ := 540
abbrev LT10k : ℕ := 10000
abbrev sT10k : ℕ := 170
abbrev DT10k : ℕ := 98020800
abbrev yT10k : ℕ := 747
abbrev rankT10k : ℕ := 183265775280
abbrev nullityT10k : ℕ := 56736169045377
abbrev depthT10k : ℕ := 8

/-! ### Source kernel T15k = (550, 15000, 170) -/

abbrev mT15k : ℕ := 550
abbrev LT15k : ℕ := 15000
abbrev sT15k : ℕ := 170
abbrev DT15k : ℕ := 99836000
abbrev yT15k : ℕ := 761
abbrev rankT15k : ℕ := 288730354170
abbrev nullityT15k : ℕ := 236413037510670
abbrev depthT15k : ℕ := 12

/-! ### Source kernel T20k = (560, 20000, 170) -/

abbrev mT20k : ℕ := 560
abbrev LT20k : ℕ := 20000
abbrev sT20k : ℕ := 170
abbrev DT20k : ℕ := 101651200
abbrev yT20k : ℕ := 775
abbrev rankT20k : ℕ := 402402095160
abbrev nullityT20k : ℕ := 427848492911895
abbrev depthT20k : ℕ := 14

/-! ### Source kernel T30k = (570, 30000, 170) -/

abbrev mT30k : ℕ := 570
abbrev LT30k : ℕ := 30000
abbrev sT30k : ℕ := 170
abbrev DT30k : ℕ := 103466400
abbrev yT30k : ℕ := 789
abbrev rankT30k : ℕ := 630511727250
abbrev nullityT30k : ℕ := 825486901846260
abbrev depthT30k : ℕ := 22

/-! ### Source kernel L1 = (1200, 100000, 360) -/

abbrev mL1 : ℕ := 1200
abbrev LL1 : ℕ := 100000
abbrev sL1 : ℕ := 360
abbrev DL1 : ℕ := 217824000
abbrev yL1 : ℕ := 1661
abbrev rankL1 : ℕ := 19672498204460
abbrev nullityL1 : ℕ := 32824016747150030
abbrev depthL1 : ℕ := 50

/-! ### Source kernel L2 = (1760, 100000, 540) -/

abbrev mL2 : ℕ := 1760
abbrev LL2 : ℕ := 100000
abbrev sL2 : ℕ := 540
abbrev DL2 : ℕ := 319475200
abbrev yL2 : ℕ := 2437
abbrev rankL2 : ℕ := 62894479678030
abbrev nullityL2 : ℕ := 98869741656154847
abbrev depthL2 : ℕ := 72

/-! ### Source kernel L3 = (2320, 100000, 720) -/

abbrev mL3 : ℕ := 2320
abbrev LL3 : ℕ := 100000
abbrev sL3 : ℕ := 720
abbrev DL3 : ℕ := 421126400
abbrev yL3 : ℕ := 3212
abbrev rankL3 : ℕ := 144846693595800
abbrev nullityL3 : ℕ := 208366000154703552
abbrev depthL3 : ℕ := 80

/-! ### Source kernel L4 = (1600, 200000, 480) -/

abbrev mL4 : ℕ := 1600
abbrev LL4 : ℕ := 200000
abbrev sL4 : ℕ := 480
abbrev DL4 : ℕ := 290432000
abbrev yL4 : ℕ := 2215
abbrev rankL4 : ℕ := 93335513436880
abbrev nullityL4 : ℕ := 169689309551713640
abbrev depthL4 : ℕ := 56

/-! ### Source kernel L5 = (3120, 200000, 960) -/

abbrev mL5 : ℕ := 3120
abbrev LL5 : ℕ := 200000
abbrev sL5 : ℕ := 960
abbrev DL5 : ℕ := 566342400
abbrev yL5 : ℕ := 4320
abbrev rankL5 : ℕ := 702078387192640
abbrev nullityL5 : ℕ := 1173917541318584880
abbrev depthL5 : ℕ := 128

/-! ### Source kernel L6 = (3900, 200000, 1200) -/

abbrev mL6 : ℕ := 3900
abbrev LL6 : ℕ := 200000
abbrev sL6 : ℕ := 1200
abbrev DL6 : ℕ := 707928000
abbrev yL6 : ℕ := 5401
abbrev rankL6 : ℕ := 1368423036387800
abbrev nullityL6 : ℕ := 2147605378029326500
abbrev depthL6 : ℕ := 150

/-! ### Source kernel M1 = (2600, 300000, 800) -/

abbrev mM1 : ℕ := 2600
abbrev LM1 : ℕ := 300000
abbrev sM1 : ℕ := 800
abbrev DM1 : ℕ := 471952000
abbrev yM1 : ℕ := 3600
abbrev rankM1 : ℕ := 611531114395200
abbrev nullityM1 : ℕ := 1138451951765615400
abbrev depthM1 : ℕ := 102

/-! ### Source kernel M3 = (3100, 300000, 950) -/

abbrev mM3 : ℕ := 3100
abbrev LM3 : ℕ := 300000
abbrev sM3 : ℕ := 950
abbrev DM3 : ℕ := 562712000
abbrev yM3 : ℕ := 4293
abbrev rankM3 : ℕ := 1032289695622850
abbrev nullityM3 : ℕ := 1879915212902702273
abbrev depthM3 : ℕ := 124

/-! ### Source kernel N1 = (2600, 400000, 800) -/

abbrev mN1 : ℕ := 2600
abbrev LN1 : ℕ := 400000
abbrev sN1 : ℕ := 800
abbrev DN1 : ℕ := 471952000
abbrev yN1 : ℕ := 3600
abbrev rankN1 : ℕ := 816167924395200
abbrev nullityN1 : ℕ := 1570210864625615400
abbrev depthN1 : ℕ := 104

/-! ### Source kernel N3 = (4600, 400000, 1400) -/

abbrev mN3 : ℕ := 4600
abbrev LN3 : ℕ := 400000
abbrev sN3 : ℕ := 1400
abbrev DN3 : ℕ := 834992000
abbrev yN3 : ℕ := 6370
abbrev rankN3 : ℕ := 4469050310913300
abbrev nullityN3 : ℕ := 8038176207758867660
abbrev depthN3 : ℕ := 180

/-! ### Source kernel N4 = (5200, 400000, 1600) -/

abbrev mN4 : ℕ := 5200
abbrev LN4 : ℕ := 400000
abbrev sN4 : ℕ := 1600
abbrev DN4 : ℕ := 943904000
abbrev yN4 : ℕ := 7201
abbrev rankN4 : ℕ := 6504399142910400
abbrev nullityN4 : ℕ := 11500069849226062000
abbrev depthN4 : ℕ := 200

/-! ### Weighted degrees, ranks, nullities

The nullity statements are written with the literal kernel parameters, identical to
the per-source modules: unifying two differently written subtractions of counts
makes Lean evaluate the counts. -/

theorem sourceA_weighted : DA = mA * agreements := by decide
theorem sourceA_rank : localRankBound mA LA sA = rankA :=
  LocatorSourceKernelA.rank_eq
theorem sourceA_nullity :
    coefficientCount 13795520 131071 130000 22 - 262144 * localRankBound 76 130000 22 = 255124945551 :=
  LocatorSourceKernelA.nullity_eq

theorem sourceAux_weighted : DAux = mAux * agreements := by decide
theorem sourceAux_rank : localRankBound mAux LAux sAux = rankAux :=
  LocatorSourceKernelAux.rank_eq
theorem sourceAux_nullity :
    coefficientCount 13795520 131071 130000 23 - 262144 * localRankBound 76 130000 23 = 422421820346 :=
  LocatorSourceKernelAux.nullity_eq

theorem sourceC_weighted : DC = mC * agreements := by decide
theorem sourceC_rank : localRankBound mC LC sC = rankC :=
  LocatorSourceKernelC.rank_eq
theorem sourceC_nullity :
    coefficientCount 72608000 131071 130000 120 - 262144 * localRankBound 400 130000 120 = 1591585493643178 :=
  LocatorSourceKernelC.nullity_eq

theorem sourceS2_weighted : DS2 = mS2 * agreements := by decide
theorem sourceS2_rank : localRankBound mS2 LS2 sS2 = rankS2 :=
  LocatorSourceKernelS2.rank_eq
theorem sourceS2_nullity :
    coefficientCount 90760000 131071 1000000 150 - 262144 * localRankBound 500 1000000 150 = 26099605139687297 :=
  LocatorSourceKernelS2.nullity_eq

theorem sourceS3_weighted : DS3 = mS3 * agreements := by decide
theorem sourceS3_rank : localRankBound mS3 LS3 sS3 = rankS3 :=
  LocatorSourceKernelS3.rank_eq
theorem sourceS3_nullity :
    coefficientCount 147031200 131071 350000 243 - 262144 * localRankBound 810 350000 243 = 40160939066613289 :=
  LocatorSourceKernelS3.nullity_eq

theorem sourceH3X_weighted : DH3X = mH3X * agreements := by decide
theorem sourceH3X_rank : localRankBound mH3X LH3X sH3X = rankH3X :=
  LocatorSourceKernelH3X.rank_eq
theorem sourceH3X_nullity :
    coefficientCount 147031200 131071 2000000 243 - 262144 * localRankBound 810 2000000 243 = 236385995162913289 :=
  LocatorSourceKernelH3X.nullity_eq

theorem sourceH4_weighted : DH4 = mH4 * agreements := by decide
theorem sourceH4_rank : localRankBound mH4 LH4 sH4 = rankH4 :=
  LocatorSourceKernelH4.rank_eq
theorem sourceH4_nullity :
    coefficientCount 181520000 131071 2000000 300 - 262144 * localRankBound 1000 2000000 300 = 452270055375521215 :=
  LocatorSourceKernelH4.nullity_eq

theorem sourceT10k_weighted : DT10k = mT10k * agreements := by decide
theorem sourceT10k_rank : localRankBound mT10k LT10k sT10k = rankT10k :=
  LocatorSourceKernelT10k.rank_eq
theorem sourceT10k_nullity :
    coefficientCount 98020800 131071 10000 170 - 262144 * localRankBound 540 10000 170 = 56736169045377 :=
  LocatorSourceKernelT10k.nullity_eq

theorem sourceT15k_weighted : DT15k = mT15k * agreements := by decide
theorem sourceT15k_rank : localRankBound mT15k LT15k sT15k = rankT15k :=
  LocatorSourceKernelT15k.rank_eq
theorem sourceT15k_nullity :
    coefficientCount 99836000 131071 15000 170 - 262144 * localRankBound 550 15000 170 = 236413037510670 :=
  LocatorSourceKernelT15k.nullity_eq

theorem sourceT20k_weighted : DT20k = mT20k * agreements := by decide
theorem sourceT20k_rank : localRankBound mT20k LT20k sT20k = rankT20k :=
  LocatorSourceKernelT20k.rank_eq
theorem sourceT20k_nullity :
    coefficientCount 101651200 131071 20000 170 - 262144 * localRankBound 560 20000 170 = 427848492911895 :=
  LocatorSourceKernelT20k.nullity_eq

theorem sourceT30k_weighted : DT30k = mT30k * agreements := by decide
theorem sourceT30k_rank : localRankBound mT30k LT30k sT30k = rankT30k :=
  LocatorSourceKernelT30k.rank_eq
theorem sourceT30k_nullity :
    coefficientCount 103466400 131071 30000 170 - 262144 * localRankBound 570 30000 170 = 825486901846260 :=
  LocatorSourceKernelT30k.nullity_eq

theorem sourceL1_weighted : DL1 = mL1 * agreements := by decide
theorem sourceL1_rank : localRankBound mL1 LL1 sL1 = rankL1 :=
  LocatorSourceKernelL1.rank_eq
theorem sourceL1_nullity :
    coefficientCount 217824000 131071 100000 360 - 262144 * localRankBound 1200 100000 360 = 32824016747150030 :=
  LocatorSourceKernelL1.nullity_eq

theorem sourceL2_weighted : DL2 = mL2 * agreements := by decide
theorem sourceL2_rank : localRankBound mL2 LL2 sL2 = rankL2 :=
  LocatorSourceKernelL2.rank_eq
theorem sourceL2_nullity :
    coefficientCount 319475200 131071 100000 540 - 262144 * localRankBound 1760 100000 540 = 98869741656154847 :=
  LocatorSourceKernelL2.nullity_eq

theorem sourceL3_weighted : DL3 = mL3 * agreements := by decide
theorem sourceL3_rank : localRankBound mL3 LL3 sL3 = rankL3 :=
  LocatorSourceKernelL3.rank_eq
theorem sourceL3_nullity :
    coefficientCount 421126400 131071 100000 720 - 262144 * localRankBound 2320 100000 720 = 208366000154703552 :=
  LocatorSourceKernelL3.nullity_eq

theorem sourceL4_weighted : DL4 = mL4 * agreements := by decide
theorem sourceL4_rank : localRankBound mL4 LL4 sL4 = rankL4 :=
  LocatorSourceKernelL4.rank_eq
theorem sourceL4_nullity :
    coefficientCount 290432000 131071 200000 480 - 262144 * localRankBound 1600 200000 480 = 169689309551713640 :=
  LocatorSourceKernelL4.nullity_eq

theorem sourceL5_weighted : DL5 = mL5 * agreements := by decide
theorem sourceL5_rank : localRankBound mL5 LL5 sL5 = rankL5 :=
  LocatorSourceKernelL5.rank_eq
theorem sourceL5_nullity :
    coefficientCount 566342400 131071 200000 960 - 262144 * localRankBound 3120 200000 960 = 1173917541318584880 :=
  LocatorSourceKernelL5.nullity_eq

theorem sourceL6_weighted : DL6 = mL6 * agreements := by decide
theorem sourceL6_rank : localRankBound mL6 LL6 sL6 = rankL6 :=
  LocatorSourceKernelL6.rank_eq
theorem sourceL6_nullity :
    coefficientCount 707928000 131071 200000 1200 - 262144 * localRankBound 3900 200000 1200 = 2147605378029326500 :=
  LocatorSourceKernelL6.nullity_eq

theorem sourceM1_weighted : DM1 = mM1 * agreements := by decide
theorem sourceM1_rank : localRankBound mM1 LM1 sM1 = rankM1 :=
  LocatorSourceKernelM1.rank_eq
theorem sourceM1_nullity :
    coefficientCount 471952000 131071 300000 800 - 262144 * localRankBound 2600 300000 800 = 1138451951765615400 :=
  LocatorSourceKernelM1.nullity_eq

theorem sourceM3_weighted : DM3 = mM3 * agreements := by decide
theorem sourceM3_rank : localRankBound mM3 LM3 sM3 = rankM3 :=
  LocatorSourceKernelM3.rank_eq
theorem sourceM3_nullity :
    coefficientCount 562712000 131071 300000 950 - 262144 * localRankBound 3100 300000 950 = 1879915212902702273 :=
  LocatorSourceKernelM3.nullity_eq

theorem sourceN1_weighted : DN1 = mN1 * agreements := by decide
theorem sourceN1_rank : localRankBound mN1 LN1 sN1 = rankN1 :=
  LocatorSourceKernelN1.rank_eq
theorem sourceN1_nullity :
    coefficientCount 471952000 131071 400000 800 - 262144 * localRankBound 2600 400000 800 = 1570210864625615400 :=
  LocatorSourceKernelN1.nullity_eq

theorem sourceN3_weighted : DN3 = mN3 * agreements := by decide
theorem sourceN3_rank : localRankBound mN3 LN3 sN3 = rankN3 :=
  LocatorSourceKernelN3.rank_eq
theorem sourceN3_nullity :
    coefficientCount 834992000 131071 400000 1400 - 262144 * localRankBound 4600 400000 1400 = 8038176207758867660 :=
  LocatorSourceKernelN3.nullity_eq

theorem sourceN4_weighted : DN4 = mN4 * agreements := by decide
theorem sourceN4_rank : localRankBound mN4 LN4 sN4 = rankN4 :=
  LocatorSourceKernelN4.rank_eq
theorem sourceN4_nullity :
    coefficientCount 943904000 131071 400000 1600 - 262144 * localRankBound 5200 400000 1600 = 11500069849226062000 :=
  LocatorSourceKernelN4.nullity_eq

/-! ### Finrank lower bounds -/

private theorem kernel_finrank_lower
    (D L s m value : ℕ)
    (hvalue : coefficientCount D 131071 L s - 262144 * localRankBound m L s = value)
    (u0 u1 : I → K) :
    value ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    D 131071 L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hvalue ▸ hlo'
theorem sourceA_finrank_lower_bound (u0 u1 : I → K) :
    nullityA ≤ Module.finrank K
      (ConstraintKernel (K := K) DA w LA sA mA IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 13795520 130000 22 76 255124945551 sourceA_nullity u0 u1

theorem sourceAux_finrank_lower_bound (u0 u1 : I → K) :
    nullityAux ≤ Module.finrank K
      (ConstraintKernel (K := K) DAux w LAux sAux mAux IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 13795520 130000 23 76 422421820346 sourceAux_nullity u0 u1

theorem sourceC_finrank_lower_bound (u0 u1 : I → K) :
    nullityC ≤ Module.finrank K
      (ConstraintKernel (K := K) DC w LC sC mC IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 72608000 130000 120 400 1591585493643178 sourceC_nullity u0 u1

theorem sourceS2_finrank_lower_bound (u0 u1 : I → K) :
    nullityS2 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS2 w LS2 sS2 mS2 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 90760000 1000000 150 500 26099605139687297 sourceS2_nullity u0 u1

theorem sourceS3_finrank_lower_bound (u0 u1 : I → K) :
    nullityS3 ≤ Module.finrank K
      (ConstraintKernel (K := K) DS3 w LS3 sS3 mS3 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 147031200 350000 243 810 40160939066613289 sourceS3_nullity u0 u1

theorem sourceH3X_finrank_lower_bound (u0 u1 : I → K) :
    nullityH3X ≤ Module.finrank K
      (ConstraintKernel (K := K) DH3X w LH3X sH3X mH3X IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 147031200 2000000 243 810 236385995162913289 sourceH3X_nullity u0 u1

theorem sourceH4_finrank_lower_bound (u0 u1 : I → K) :
    nullityH4 ≤ Module.finrank K
      (ConstraintKernel (K := K) DH4 w LH4 sH4 mH4 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 181520000 2000000 300 1000 452270055375521215 sourceH4_nullity u0 u1

theorem sourceT10k_finrank_lower_bound (u0 u1 : I → K) :
    nullityT10k ≤ Module.finrank K
      (ConstraintKernel (K := K) DT10k w LT10k sT10k mT10k IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 98020800 10000 170 540 56736169045377 sourceT10k_nullity u0 u1

theorem sourceT15k_finrank_lower_bound (u0 u1 : I → K) :
    nullityT15k ≤ Module.finrank K
      (ConstraintKernel (K := K) DT15k w LT15k sT15k mT15k IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 99836000 15000 170 550 236413037510670 sourceT15k_nullity u0 u1

theorem sourceT20k_finrank_lower_bound (u0 u1 : I → K) :
    nullityT20k ≤ Module.finrank K
      (ConstraintKernel (K := K) DT20k w LT20k sT20k mT20k IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 101651200 20000 170 560 427848492911895 sourceT20k_nullity u0 u1

theorem sourceT30k_finrank_lower_bound (u0 u1 : I → K) :
    nullityT30k ≤ Module.finrank K
      (ConstraintKernel (K := K) DT30k w LT30k sT30k mT30k IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 103466400 30000 170 570 825486901846260 sourceT30k_nullity u0 u1

theorem sourceL1_finrank_lower_bound (u0 u1 : I → K) :
    nullityL1 ≤ Module.finrank K
      (ConstraintKernel (K := K) DL1 w LL1 sL1 mL1 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 217824000 100000 360 1200 32824016747150030 sourceL1_nullity u0 u1

theorem sourceL2_finrank_lower_bound (u0 u1 : I → K) :
    nullityL2 ≤ Module.finrank K
      (ConstraintKernel (K := K) DL2 w LL2 sL2 mL2 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 319475200 100000 540 1760 98869741656154847 sourceL2_nullity u0 u1

theorem sourceL3_finrank_lower_bound (u0 u1 : I → K) :
    nullityL3 ≤ Module.finrank K
      (ConstraintKernel (K := K) DL3 w LL3 sL3 mL3 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 421126400 100000 720 2320 208366000154703552 sourceL3_nullity u0 u1

theorem sourceL4_finrank_lower_bound (u0 u1 : I → K) :
    nullityL4 ≤ Module.finrank K
      (ConstraintKernel (K := K) DL4 w LL4 sL4 mL4 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 290432000 200000 480 1600 169689309551713640 sourceL4_nullity u0 u1

theorem sourceL5_finrank_lower_bound (u0 u1 : I → K) :
    nullityL5 ≤ Module.finrank K
      (ConstraintKernel (K := K) DL5 w LL5 sL5 mL5 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 566342400 200000 960 3120 1173917541318584880 sourceL5_nullity u0 u1

theorem sourceL6_finrank_lower_bound (u0 u1 : I → K) :
    nullityL6 ≤ Module.finrank K
      (ConstraintKernel (K := K) DL6 w LL6 sL6 mL6 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 707928000 200000 1200 3900 2147605378029326500 sourceL6_nullity u0 u1

theorem sourceM1_finrank_lower_bound (u0 u1 : I → K) :
    nullityM1 ≤ Module.finrank K
      (ConstraintKernel (K := K) DM1 w LM1 sM1 mM1 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 471952000 300000 800 2600 1138451951765615400 sourceM1_nullity u0 u1

theorem sourceM3_finrank_lower_bound (u0 u1 : I → K) :
    nullityM3 ≤ Module.finrank K
      (ConstraintKernel (K := K) DM3 w LM3 sM3 mM3 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 562712000 300000 950 3100 1879915212902702273 sourceM3_nullity u0 u1

theorem sourceN1_finrank_lower_bound (u0 u1 : I → K) :
    nullityN1 ≤ Module.finrank K
      (ConstraintKernel (K := K) DN1 w LN1 sN1 mN1 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 471952000 400000 800 2600 1570210864625615400 sourceN1_nullity u0 u1

theorem sourceN3_finrank_lower_bound (u0 u1 : I → K) :
    nullityN3 ≤ Module.finrank K
      (ConstraintKernel (K := K) DN3 w LN3 sN3 mN3 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 834992000 400000 1400 4600 8038176207758867660 sourceN3_nullity u0 u1

theorem sourceN4_finrank_lower_bound (u0 u1 : I → K) :
    nullityN4 ≤ Module.finrank K
      (ConstraintKernel (K := K) DN4 w LN4 sN4 mN4 IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 943904000 400000 1600 5200 11500069849226062000 sourceN4_nullity u0 u1

/-! ### Factorial casts for the stage tower -/

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

/-- The shape the reference port uses; the bound is the grid's `depthCap` (200). -/
theorem factorial_cast_ne_zero_of_le_thirty
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j ≤ 200) : (j.factorial : E) ≠ 0 :=
  factorial_cast_ne_zero j (by omega)

/-! ### Stage capacity, positivity and shape (equality holds for every j ≤ m) -/

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

theorem sourceH3X_stage_capacity (j : ℕ) (hj : j ≤ depthH3X) :
    DH3X - j * delta = (mH3X - j) * agreements + j * (w - 1) := by
  unfold DH3X delta mH3X agreements w depthH3X at *
  omega

theorem sourceH3X_low_positive (j : ℕ) (hj : j ≤ depthH3X) : 0 < DH3X - j * delta := by
  unfold DH3X delta depthH3X at *
  omega

theorem sourceH3X_shape : DH3X + sH3X ≤ w * (yH3X + 1) := by decide

theorem sourceH4_stage_capacity (j : ℕ) (hj : j ≤ depthH4) :
    DH4 - j * delta = (mH4 - j) * agreements + j * (w - 1) := by
  unfold DH4 delta mH4 agreements w depthH4 at *
  omega

theorem sourceH4_low_positive (j : ℕ) (hj : j ≤ depthH4) : 0 < DH4 - j * delta := by
  unfold DH4 delta depthH4 at *
  omega

theorem sourceH4_shape : DH4 + sH4 ≤ w * (yH4 + 1) := by decide

theorem sourceT10k_stage_capacity (j : ℕ) (hj : j ≤ depthT10k) :
    DT10k - j * delta = (mT10k - j) * agreements + j * (w - 1) := by
  unfold DT10k delta mT10k agreements w depthT10k at *
  omega

theorem sourceT10k_low_positive (j : ℕ) (hj : j ≤ depthT10k) : 0 < DT10k - j * delta := by
  unfold DT10k delta depthT10k at *
  omega

theorem sourceT10k_shape : DT10k + sT10k ≤ w * (yT10k + 1) := by decide

theorem sourceT15k_stage_capacity (j : ℕ) (hj : j ≤ depthT15k) :
    DT15k - j * delta = (mT15k - j) * agreements + j * (w - 1) := by
  unfold DT15k delta mT15k agreements w depthT15k at *
  omega

theorem sourceT15k_low_positive (j : ℕ) (hj : j ≤ depthT15k) : 0 < DT15k - j * delta := by
  unfold DT15k delta depthT15k at *
  omega

theorem sourceT15k_shape : DT15k + sT15k ≤ w * (yT15k + 1) := by decide

theorem sourceT20k_stage_capacity (j : ℕ) (hj : j ≤ depthT20k) :
    DT20k - j * delta = (mT20k - j) * agreements + j * (w - 1) := by
  unfold DT20k delta mT20k agreements w depthT20k at *
  omega

theorem sourceT20k_low_positive (j : ℕ) (hj : j ≤ depthT20k) : 0 < DT20k - j * delta := by
  unfold DT20k delta depthT20k at *
  omega

theorem sourceT20k_shape : DT20k + sT20k ≤ w * (yT20k + 1) := by decide

theorem sourceT30k_stage_capacity (j : ℕ) (hj : j ≤ depthT30k) :
    DT30k - j * delta = (mT30k - j) * agreements + j * (w - 1) := by
  unfold DT30k delta mT30k agreements w depthT30k at *
  omega

theorem sourceT30k_low_positive (j : ℕ) (hj : j ≤ depthT30k) : 0 < DT30k - j * delta := by
  unfold DT30k delta depthT30k at *
  omega

theorem sourceT30k_shape : DT30k + sT30k ≤ w * (yT30k + 1) := by decide

theorem sourceL1_stage_capacity (j : ℕ) (hj : j ≤ depthL1) :
    DL1 - j * delta = (mL1 - j) * agreements + j * (w - 1) := by
  unfold DL1 delta mL1 agreements w depthL1 at *
  omega

theorem sourceL1_low_positive (j : ℕ) (hj : j ≤ depthL1) : 0 < DL1 - j * delta := by
  unfold DL1 delta depthL1 at *
  omega

theorem sourceL1_shape : DL1 + sL1 ≤ w * (yL1 + 1) := by decide

theorem sourceL2_stage_capacity (j : ℕ) (hj : j ≤ depthL2) :
    DL2 - j * delta = (mL2 - j) * agreements + j * (w - 1) := by
  unfold DL2 delta mL2 agreements w depthL2 at *
  omega

theorem sourceL2_low_positive (j : ℕ) (hj : j ≤ depthL2) : 0 < DL2 - j * delta := by
  unfold DL2 delta depthL2 at *
  omega

theorem sourceL2_shape : DL2 + sL2 ≤ w * (yL2 + 1) := by decide

theorem sourceL3_stage_capacity (j : ℕ) (hj : j ≤ depthL3) :
    DL3 - j * delta = (mL3 - j) * agreements + j * (w - 1) := by
  unfold DL3 delta mL3 agreements w depthL3 at *
  omega

theorem sourceL3_low_positive (j : ℕ) (hj : j ≤ depthL3) : 0 < DL3 - j * delta := by
  unfold DL3 delta depthL3 at *
  omega

theorem sourceL3_shape : DL3 + sL3 ≤ w * (yL3 + 1) := by decide

theorem sourceL4_stage_capacity (j : ℕ) (hj : j ≤ depthL4) :
    DL4 - j * delta = (mL4 - j) * agreements + j * (w - 1) := by
  unfold DL4 delta mL4 agreements w depthL4 at *
  omega

theorem sourceL4_low_positive (j : ℕ) (hj : j ≤ depthL4) : 0 < DL4 - j * delta := by
  unfold DL4 delta depthL4 at *
  omega

theorem sourceL4_shape : DL4 + sL4 ≤ w * (yL4 + 1) := by decide

theorem sourceL5_stage_capacity (j : ℕ) (hj : j ≤ depthL5) :
    DL5 - j * delta = (mL5 - j) * agreements + j * (w - 1) := by
  unfold DL5 delta mL5 agreements w depthL5 at *
  omega

theorem sourceL5_low_positive (j : ℕ) (hj : j ≤ depthL5) : 0 < DL5 - j * delta := by
  unfold DL5 delta depthL5 at *
  omega

theorem sourceL5_shape : DL5 + sL5 ≤ w * (yL5 + 1) := by decide

theorem sourceL6_stage_capacity (j : ℕ) (hj : j ≤ depthL6) :
    DL6 - j * delta = (mL6 - j) * agreements + j * (w - 1) := by
  unfold DL6 delta mL6 agreements w depthL6 at *
  omega

theorem sourceL6_low_positive (j : ℕ) (hj : j ≤ depthL6) : 0 < DL6 - j * delta := by
  unfold DL6 delta depthL6 at *
  omega

theorem sourceL6_shape : DL6 + sL6 ≤ w * (yL6 + 1) := by decide

theorem sourceM1_stage_capacity (j : ℕ) (hj : j ≤ depthM1) :
    DM1 - j * delta = (mM1 - j) * agreements + j * (w - 1) := by
  unfold DM1 delta mM1 agreements w depthM1 at *
  omega

theorem sourceM1_low_positive (j : ℕ) (hj : j ≤ depthM1) : 0 < DM1 - j * delta := by
  unfold DM1 delta depthM1 at *
  omega

theorem sourceM1_shape : DM1 + sM1 ≤ w * (yM1 + 1) := by decide

theorem sourceM3_stage_capacity (j : ℕ) (hj : j ≤ depthM3) :
    DM3 - j * delta = (mM3 - j) * agreements + j * (w - 1) := by
  unfold DM3 delta mM3 agreements w depthM3 at *
  omega

theorem sourceM3_low_positive (j : ℕ) (hj : j ≤ depthM3) : 0 < DM3 - j * delta := by
  unfold DM3 delta depthM3 at *
  omega

theorem sourceM3_shape : DM3 + sM3 ≤ w * (yM3 + 1) := by decide

theorem sourceN1_stage_capacity (j : ℕ) (hj : j ≤ depthN1) :
    DN1 - j * delta = (mN1 - j) * agreements + j * (w - 1) := by
  unfold DN1 delta mN1 agreements w depthN1 at *
  omega

theorem sourceN1_low_positive (j : ℕ) (hj : j ≤ depthN1) : 0 < DN1 - j * delta := by
  unfold DN1 delta depthN1 at *
  omega

theorem sourceN1_shape : DN1 + sN1 ≤ w * (yN1 + 1) := by decide

theorem sourceN3_stage_capacity (j : ℕ) (hj : j ≤ depthN3) :
    DN3 - j * delta = (mN3 - j) * agreements + j * (w - 1) := by
  unfold DN3 delta mN3 agreements w depthN3 at *
  omega

theorem sourceN3_low_positive (j : ℕ) (hj : j ≤ depthN3) : 0 < DN3 - j * delta := by
  unfold DN3 delta depthN3 at *
  omega

theorem sourceN3_shape : DN3 + sN3 ≤ w * (yN3 + 1) := by decide

theorem sourceN4_stage_capacity (j : ℕ) (hj : j ≤ depthN4) :
    DN4 - j * delta = (mN4 - j) * agreements + j * (w - 1) := by
  unfold DN4 delta mN4 agreements w depthN4 at *
  omega

theorem sourceN4_low_positive (j : ℕ) (hj : j ≤ depthN4) : 0 < DN4 - j * delta := by
  unfold DN4 delta depthN4 at *
  omega

theorem sourceN4_shape : DN4 + sN4 ≤ w * (yN4 + 1) := by decide

end

end ProximityPrize.SubmissionLower.LocatorHelperArithmeticGeneric

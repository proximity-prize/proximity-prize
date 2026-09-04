import ProximityPrize.SubmissionLower.CyclicFourRankBridge
import ProximityPrize.SubmissionLower.LocatorR1200Source6803
import ProximityPrize.SubmissionLower.LocatorR1Rank
import ProximityPrize.SubmissionLower.LocatorSplit500Rank
import ProximityPrize.SubmissionLower.LocatorSplit390Rank

/-!
# Exact rank-saving targets for the 68.03 factor cascade

The four 68.02 phase profiles remain geometrically preferable at agreement
`181363`, but their elementary `source - n * localRankBound` nullities shrink.
This file records the exact 68.03 dimensions and turns any improved global
range estimate into the old, phase-certificate-compatible kernel dimensions.

No improved range estimate is assumed here.  The hypotheses of the four final
theorems are the precise finite-geometry obligations still to be discharged.
-/

namespace ProximityPrize.SubmissionLower.LocatorCascadeRankBridge6803

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic
open CyclicFourFibre CyclicFourIncidence
open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

/-- If the true range saves `saving` dimensions against `localBudget`, this
converts the saving directly into a quantitative kernel lower bound. -/
theorem finrank_ker_ge_of_rank_saving
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (sourceRank localBudget saving desired : ℕ)
    (hsource : Module.finrank F V = sourceRank)
    (hsaved : Module.finrank F (LinearMap.range f) + saving ≤ localBudget)
    (hgate : desired + localBudget ≤ sourceRank + saving) :
    desired ≤ Module.finrank F (LinearMap.ker f) := by
  have hsum := f.finrank_range_add_finrank_ker
  rw [hsource] at hsum
  omega

def oldGapR1200 : ℕ := 5227117860923383312
def oldGapC : ℕ := 18811500529412710
def oldGapSplit500 : ℕ := 4161068143836058
def oldGapSplit390 : ℕ := 95423319727890

def sourceRankR1200 : ℕ := 1107150758552279760150
def localBudgetR1200 : ℕ := 1102059891539097681920
def requiredSavingR1200 : ℕ := 136250847741305082

def sourceRankC : ℕ := 4335906553882664390
def localBudgetC : ℕ := 4317628515148103680
def requiredSavingC : ℕ := 533461794852000

def sourceRankSplit500 : ℕ := 1283130288763499898
def localBudgetSplit500 : ℕ := 1279126829691043840
def requiredSavingSplit500 : ℕ := 157609071380000

def sourceRankSplit390 : ℕ := 35441500377123610
def localBudgetSplit390 : ℕ := 35350426715422720
def requiredSavingSplit390 : ℕ := 4349658027000

theorem coefficientCountC_exact :
    coefficientCount 217635600 131071 82100 370 = sourceRankC := by
  change coefficientCount (1660 * 131071 + 57740) 131071 82100 370 =
    sourceRankC
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1660 57740 131071 82100 370 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial,
    sourceRankC]

theorem coefficientCountSplit500_exact :
    coefficientCount 181363000 131071 42000 310 = sourceRankSplit500 := by
  change coefficientCount (1383 * 131071 + 91807) 131071 42000 310 =
    sourceRankSplit500
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1383 91807 131071 42000 310 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial,
    sourceRankSplit500]

theorem coefficientCountSplit390_exact :
    coefficientCount 70731570 131071 19500 120 = sourceRankSplit390 := by
  change coefficientCount (539 * 131071 + 84301) 131071 19500 120 =
    sourceRankSplit390
  rw [coefficientCount_eq_oneResidueCoefficientCount
    539 84301 131071 19500 120 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial,
    sourceRankSplit390]

theorem localBudgetR1200_exact :
    262144 * localRankBound 4800 328400 1480 = localBudgetR1200 := by
  rw [LocatorR1200Rank.localRankBound_exact]
  norm_num [localBudgetR1200]

theorem localBudgetC_exact :
    262144 * localRankBound 1200 82100 370 = localBudgetC := by
  rw [LocatorR1Rank.localRankBound_exact]
  norm_num [localBudgetC]

theorem localBudgetSplit500_exact :
    262144 * localRankBound 1000 42000 310 = localBudgetSplit500 := by
  rw [LocatorSplit500Rank.localRankBound_exact]
  norm_num [localBudgetSplit500]

theorem localBudgetSplit390_exact :
    262144 * localRankBound 390 19500 120 = localBudgetSplit390 := by
  rw [LocatorSplit390Rank.localRankBound_exact]
  norm_num [localBudgetSplit390]

abbrev mapR1200 (u0 u1 : I → K) :=
  RCN100.constraintMap K 870542400 131071 328400 1480 4800
    IRSProfile.domain u0 u1

abbrev mapC (u0 u1 : I → K) :=
  RCN100.constraintMap K 217635600 131071 82100 370 1200
    IRSProfile.domain u0 u1

abbrev mapSplit500 (u0 u1 : I → K) :=
  RCN100.constraintMap K 181363000 131071 42000 310 1000
    IRSProfile.domain u0 u1

abbrev mapSplit390 (u0 u1 : I → K) :=
  RCN100.constraintMap K 70731570 131071 19500 120 390
    IRSProfile.domain u0 u1

theorem restoredGapR1200_gate :
    oldGapR1200 + localBudgetR1200 ≤
      sourceRankR1200 + requiredSavingR1200 := by
  norm_num [oldGapR1200, localBudgetR1200, sourceRankR1200,
    requiredSavingR1200]

theorem restoredGapC_gate :
    oldGapC + localBudgetC ≤ sourceRankC + requiredSavingC := by
  norm_num [oldGapC, localBudgetC, sourceRankC, requiredSavingC]

theorem restoredGapSplit500_gate :
    oldGapSplit500 + localBudgetSplit500 ≤
      sourceRankSplit500 + requiredSavingSplit500 := by
  norm_num [oldGapSplit500, localBudgetSplit500, sourceRankSplit500,
    requiredSavingSplit500]

theorem restoredGapSplit390_gate :
    oldGapSplit390 + localBudgetSplit390 ≤
      sourceRankSplit390 + requiredSavingSplit390 := by
  norm_num [oldGapSplit390, localBudgetSplit390, sourceRankSplit390,
    requiredSavingSplit390]

/-- A genuine global range saving of the stated size restores exactly the
kernel dimension consumed by the promoted R1200 phase certificate. -/
theorem restoredGapR1200_of_range_saving (u0 u1 : I → K)
    (hsaved : Module.finrank K (LinearMap.range (mapR1200 u0 u1)) +
      requiredSavingR1200 ≤ localBudgetR1200) :
    oldGapR1200 ≤ Module.finrank K (LinearMap.ker (mapR1200 u0 u1)) := by
  apply finrank_ker_ge_of_rank_saving (mapR1200 u0 u1)
    sourceRankR1200 localBudgetR1200 requiredSavingR1200 oldGapR1200
  · rw [Module.finrank_fintype_fun_eq_card, RCN100.coefficient_index_card]
    simpa only [sourceRankR1200] using
      LocatorR1200Source6803.coefficientCount_exact
  · exact hsaved
  · exact restoredGapR1200_gate

theorem restoredGapC_of_range_saving (u0 u1 : I → K)
    (hsaved : Module.finrank K (LinearMap.range (mapC u0 u1)) +
      requiredSavingC ≤ localBudgetC) :
    oldGapC ≤ Module.finrank K (LinearMap.ker (mapC u0 u1)) := by
  apply finrank_ker_ge_of_rank_saving (mapC u0 u1)
    sourceRankC localBudgetC requiredSavingC oldGapC
  · rw [Module.finrank_fintype_fun_eq_card, RCN100.coefficient_index_card,
      coefficientCountC_exact]
  · exact hsaved
  · exact restoredGapC_gate

theorem restoredGapSplit500_of_range_saving (u0 u1 : I → K)
    (hsaved : Module.finrank K (LinearMap.range (mapSplit500 u0 u1)) +
      requiredSavingSplit500 ≤ localBudgetSplit500) :
    oldGapSplit500 ≤
      Module.finrank K (LinearMap.ker (mapSplit500 u0 u1)) := by
  apply finrank_ker_ge_of_rank_saving (mapSplit500 u0 u1)
    sourceRankSplit500 localBudgetSplit500 requiredSavingSplit500 oldGapSplit500
  · rw [Module.finrank_fintype_fun_eq_card, RCN100.coefficient_index_card,
      coefficientCountSplit500_exact]
  · exact hsaved
  · exact restoredGapSplit500_gate

theorem restoredGapSplit390_of_range_saving (u0 u1 : I → K)
    (hsaved : Module.finrank K (LinearMap.range (mapSplit390 u0 u1)) +
      requiredSavingSplit390 ≤ localBudgetSplit390) :
    oldGapSplit390 ≤
      Module.finrank K (LinearMap.ker (mapSplit390 u0 u1)) := by
  apply finrank_ker_ge_of_rank_saving (mapSplit390 u0 u1)
    sourceRankSplit390 localBudgetSplit390 requiredSavingSplit390 oldGapSplit390
  · rw [Module.finrank_fintype_fun_eq_card, RCN100.coefficient_index_card,
      coefficientCountSplit390_exact]
  · exact hsaved
  · exact restoredGapSplit390_gate

def savingPerExcessR1200 : ℕ := 2709249124920
def savingPerExcessC : ℕ := 10607500246
def savingPerExcessSplit500 : ℕ := 3133941886
def savingPerExcessSplit390 : ℕ := 86489790

theorem bundleExcess_covers_requiredSavingR1200
    (S : Finset IRSProfile.Index) (hS : 181363 ≤ S.card) :
    requiredSavingR1200 ≤
      savingPerExcessR1200 * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingR1200 ≤ savingPerExcessR1200 * 50291 := by
      norm_num [requiredSavingR1200, savingPerExcessR1200]
    _ ≤ savingPerExcessR1200 * ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessR1200
        (bundleExcess_sum_ge_6803 S hS)

theorem bundleExcess_covers_requiredSavingC
    (S : Finset IRSProfile.Index) (hS : 181363 ≤ S.card) :
    requiredSavingC ≤
      savingPerExcessC * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingC ≤ savingPerExcessC * 50291 := by
      norm_num [requiredSavingC, savingPerExcessC]
    _ ≤ savingPerExcessC * ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessC (bundleExcess_sum_ge_6803 S hS)

theorem bundleExcess_covers_requiredSavingSplit500
    (S : Finset IRSProfile.Index) (hS : 181363 ≤ S.card) :
    requiredSavingSplit500 ≤
      savingPerExcessSplit500 * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingSplit500 ≤ savingPerExcessSplit500 * 50291 := by
      norm_num [requiredSavingSplit500, savingPerExcessSplit500]
    _ ≤ savingPerExcessSplit500 *
        ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessSplit500
        (bundleExcess_sum_ge_6803 S hS)

theorem bundleExcess_covers_requiredSavingSplit390
    (S : Finset IRSProfile.Index) (hS : 181363 ≤ S.card) :
    requiredSavingSplit390 ≤
      savingPerExcessSplit390 * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingSplit390 ≤ savingPerExcessSplit390 * 50291 := by
      norm_num [requiredSavingSplit390, savingPerExcessSplit390]
    _ ≤ savingPerExcessSplit390 *
        ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessSplit390
        (bundleExcess_sum_ge_6803 S hS)

end

end ProximityPrize.SubmissionLower.LocatorCascadeRankBridge6803

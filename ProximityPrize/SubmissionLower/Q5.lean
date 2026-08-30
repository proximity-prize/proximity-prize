import ProximityPrize.SubmissionLower.Q4
import ProximityPrize.SubmissionLower.CI
namespace ProximityPrize.SubmissionLower.ContactTwoTailResidualRectangles6734Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
open ContactTwoTailParameters6734Research
open ContactTwoTailResidualGeneric6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
theorem residualValidities_of_profiles (lt ly ls us : ℕ)
   (h :
     (lt = 1260 ∧ ly = 53 ∧ ls = 11 ∧ us = 12) ∨
     (lt = 1260 ∧ ly = 53 ∧ ls = 0 ∧ us = 11) ∨
     (lt = 1260 ∧ ly = 0 ∧ ls = 11 ∧ us = 12) ∨
     (lt = 1260 ∧ ly = 0 ∧ ls = 0 ∧ us = 11) ∨
     (lt = 0 ∧ ly = 53 ∧ ls = 11 ∧ us = 12) ∨
     (lt = 0 ∧ ly = 53 ∧ ls = 0 ∧ us = 11) ∨
     (lt = 0 ∧ ly = 0 ∧ ls = 11 ∧ us = 12) ∨
     (lt = 0 ∧ ly = 0 ∧ ls = 0 ∧ us = 11) ∨
     (lt = 1260 ∧ ly = 54 ∧ ls = 10 ∧ us = 11) ∨
     (lt = 1260 ∧ ly = 54 ∧ ls = 0 ∧ us = 10) ∨
     (lt = 1260 ∧ ly = 0 ∧ ls = 10 ∧ us = 11) ∨
     (lt = 1260 ∧ ly = 0 ∧ ls = 0 ∧ us = 10) ∨
     (lt = 0 ∧ ly = 54 ∧ ls = 10 ∧ us = 11) ∨
     (lt = 0 ∧ ly = 54 ∧ ls = 0 ∧ us = 10) ∨
     (lt = 0 ∧ ly = 0 ∧ ls = 10 ∧ us = 11) ∨
     (lt = 0 ∧ ly = 0 ∧ ls = 0 ∧ us = 10)) :
   ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls) ∧
     ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls) := by
 rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
   rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;> constructor <;> constructor <;>
   norm_num [firstStage, firstPivot, secondStage, secondPivot,
     ContactTwoTailParameters6734Research.n,
     ContactTwoTailParameters6734Research.w,
     ContactTwoTailParameters6734Research.errors,
     ContactTwoTailParameters6734Research.agreements,
     ContactTwoTailParameters6734Research.prime,
     ContactTwoTailParameters6734Research.Profile.weightedCap,
     ContactTwoTailParameters6734Research.profileA,
     ContactTwoTailParameters6734Research.profileB,
     ContactTwoTailParameters6734Research.profileC,
     UnequalParameters.errors, UnequalParameters.gap,
     UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
     UnequalParameters.agreement, UnequalParameters.mixedCost,
     UnequalParameters.regularNumerator, UnequalParameters.regularCountCap,
     TightParameters.errors, TightParameters.gap, TightParameters.kappa,
     TightParameters.algebraicCap, TightParameters.implicitYCap,
     TightParameters.agreement, TightParameters.aggregateCost,
     TightParameters.coreNumerator, TightParameters.tightNumerator,
     TightParameters.countCap, dot] at *
def rectangleCost (a b s lt ly ls us : ℕ) : ℕ :=
 fixedRegularCost a b s + (fixedTightProfile a b s).countCap +
   ((firstStage lt ly ls us).regularCountCap + (firstPivot lt ls).countCap + 1) +
   ((secondStage lt ly ls us).regularCountCap + (secondPivot lt ls).countCap + 1)
theorem rectangleCost_lt_of_profiles (a b s lt ly ls us : ℕ)
   (h :
     (a = 1207 ∧ b = 41 ∧ s = 10 ∧ lt = 1260 ∧ ly = 53 ∧ ls = 11 ∧ us = 12) ∨
     (a = 1207 ∧ b = 42 ∧ s = 9 ∧ lt = 1260 ∧ ly = 53 ∧ ls = 0 ∧ us = 11) ∨
     (a = 1208 ∧ b = 40 ∧ s = 10 ∧ lt = 1260 ∧ ly = 0 ∧ ls = 11 ∧ us = 12) ∨
     (a = 1208 ∧ b = 41 ∧ s = 9 ∧ lt = 1260 ∧ ly = 0 ∧ ls = 0 ∧ us = 11) ∨
     (a = 1206 ∧ b = 41 ∧ s = 10 ∧ lt = 0 ∧ ly = 53 ∧ ls = 11 ∧ us = 12) ∨
     (a = 1206 ∧ b = 42 ∧ s = 9 ∧ lt = 0 ∧ ly = 53 ∧ ls = 0 ∧ us = 11) ∨
     (a = 1207 ∧ b = 40 ∧ s = 10 ∧ lt = 0 ∧ ly = 0 ∧ ls = 11 ∧ us = 12) ∨
     (a = 1207 ∧ b = 41 ∧ s = 9 ∧ lt = 0 ∧ ly = 0 ∧ ls = 0 ∧ us = 11) ∨
     (a = 1206 ∧ b = 43 ∧ s = 9 ∧ lt = 1260 ∧ ly = 54 ∧ ls = 10 ∧ us = 11) ∨
     (a = 1206 ∧ b = 44 ∧ s = 8 ∧ lt = 1260 ∧ ly = 54 ∧ ls = 0 ∧ us = 10) ∨
     (a = 1207 ∧ b = 42 ∧ s = 9 ∧ lt = 1260 ∧ ly = 0 ∧ ls = 10 ∧ us = 11) ∨
     (a = 1207 ∧ b = 43 ∧ s = 8 ∧ lt = 1260 ∧ ly = 0 ∧ ls = 0 ∧ us = 10) ∨
     (a = 1205 ∧ b = 43 ∧ s = 9 ∧ lt = 0 ∧ ly = 54 ∧ ls = 10 ∧ us = 11) ∨
     (a = 1205 ∧ b = 44 ∧ s = 8 ∧ lt = 0 ∧ ly = 54 ∧ ls = 0 ∧ us = 10) ∨
     (a = 1206 ∧ b = 42 ∧ s = 9 ∧ lt = 0 ∧ ly = 0 ∧ ls = 10 ∧ us = 11) ∨
     (a = 1206 ∧ b = 43 ∧ s = 8 ∧ lt = 0 ∧ ly = 0 ∧ ls = 0 ∧ us = 10)) :
   rectangleCost a b s lt ly ls us < mcaBudget := by
 rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
   rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
   norm_num [rectangleCost, fixedRegularCost, fixedTightProfile,
     ContactTwoTailFixedSelectedGeneric6734Research.fixedProfile,
     ContactTwoTailFixedSelectedGeneric6734Research.fixedFlag,
     ContactTwoTailFixedSelectedGeneric6734Research.firstTail,
     ContactTwoTailFixedSelectedGeneric6734Research.secondTail,
     ContactMovingAgreementCertificate6719Research.support,
     ContactReducedTaylorProfileResearch.reducedResidualAgreementFlag,
     ContactReducedTaylorProfileResearch.reducedAgreementDirection,
     ContactMovingPositiveLedger6719Research.centreFlag,
     ContactMovingPositiveLedger6719Research.directionFlag,
     ContactMovingPositiveLedger6719Research.surfaceFlag,
     ContactFlagBezout6543Research.flagMixed,
     ContactFlagBezout6543Research.unitZFlag,
     ContactFlagBezout6543Research.unitYZFlag,
     ContactFlagBezout6543Research.add_zOnly,
     ContactFlagBezout6543Research.add_yz,
     ContactFlagBezout6543Research.add_all,
     ContactFlagBezout6543Research.nsmul_zOnly,
     ContactFlagBezout6543Research.nsmul_yz,
     ContactFlagBezout6543Research.nsmul_all,
     ContactTwoTailParameters6734Research.mcaBudget,
     ContactTwoTailParameters6734Research.capacity,
     ContactTwoTailParameters6734Research.listBudget,
     firstStage, firstPivot, secondStage, secondPivot,
     ContactTwoTailParameters6734Research.n,
     ContactTwoTailParameters6734Research.w,
     ContactTwoTailParameters6734Research.errors,
     ContactTwoTailParameters6734Research.agreements,
     ContactTwoTailParameters6734Research.prime,
     ContactTwoTailParameters6734Research.Profile.weightedCap,
     ContactTwoTailParameters6734Research.profileA,
     ContactTwoTailParameters6734Research.profileB,
     ContactTwoTailParameters6734Research.profileC,
     UnequalParameters.errors, UnequalParameters.gap,
     UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
     UnequalParameters.agreement, UnequalParameters.mixedCost,
     UnequalParameters.regularNumerator, UnequalParameters.regularCountCap,
     TightParameters.errors, TightParameters.gap, TightParameters.kappa,
     TightParameters.algebraicCap, TightParameters.implicitYCap,
     TightParameters.agreement, TightParameters.aggregateCost,
     TightParameters.coreNumerator, TightParameters.tightNumerator,
     TightParameters.countCap, dot]
theorem firstValidYS111 : ResidualValidity (firstStage 1260 53 11 12)
   (firstPivot 1260 11) :=
 (residualValidities_of_profiles 1260 53 11 12 (by simp)).1
theorem secondValidYS111 : ResidualValidity (secondStage 1260 53 11 12)
   (secondPivot 1260 11) :=
 (residualValidities_of_profiles 1260 53 11 12 (by simp)).2
theorem firstValidYS110 : ResidualValidity (firstStage 1260 53 0 11)
   (firstPivot 1260 0) := (residualValidities_of_profiles 1260 53 0 11 (by simp)).1
theorem secondValidYS110 : ResidualValidity (secondStage 1260 53 0 11)
   (secondPivot 1260 0) := (residualValidities_of_profiles 1260 53 0 11 (by simp)).2
theorem firstValidYS101 : ResidualValidity (firstStage 1260 0 11 12)
   (firstPivot 1260 11) := (residualValidities_of_profiles 1260 0 11 12 (by simp)).1
theorem secondValidYS101 : ResidualValidity (secondStage 1260 0 11 12)
   (secondPivot 1260 11) := (residualValidities_of_profiles 1260 0 11 12 (by simp)).2
theorem firstValidYS100 : ResidualValidity (firstStage 1260 0 0 11)
   (firstPivot 1260 0) := (residualValidities_of_profiles 1260 0 0 11 (by simp)).1
theorem secondValidYS100 : ResidualValidity (secondStage 1260 0 0 11)
   (secondPivot 1260 0) := (residualValidities_of_profiles 1260 0 0 11 (by simp)).2
theorem firstValidYS011 : ResidualValidity (firstStage 0 53 11 12)
   (firstPivot 0 11) := (residualValidities_of_profiles 0 53 11 12 (by simp)).1
theorem secondValidYS011 : ResidualValidity (secondStage 0 53 11 12)
   (secondPivot 0 11) := (residualValidities_of_profiles 0 53 11 12 (by simp)).2
theorem firstValidYS010 : ResidualValidity (firstStage 0 53 0 11)
   (firstPivot 0 0) := (residualValidities_of_profiles 0 53 0 11 (by simp)).1
theorem secondValidYS010 : ResidualValidity (secondStage 0 53 0 11)
   (secondPivot 0 0) := (residualValidities_of_profiles 0 53 0 11 (by simp)).2
theorem firstValidYS001 : ResidualValidity (firstStage 0 0 11 12)
   (firstPivot 0 11) := (residualValidities_of_profiles 0 0 11 12 (by simp)).1
theorem secondValidYS001 : ResidualValidity (secondStage 0 0 11 12)
   (secondPivot 0 11) := (residualValidities_of_profiles 0 0 11 12 (by simp)).2
theorem firstValidYS000 : ResidualValidity (firstStage 0 0 0 11)
   (firstPivot 0 0) := (residualValidities_of_profiles 0 0 0 11 (by simp)).1
theorem secondValidYS000 : ResidualValidity (secondStage 0 0 0 11)
   (secondPivot 0 0) := (residualValidities_of_profiles 0 0 0 11 (by simp)).2
theorem firstValidS111 : ResidualValidity (firstStage 1260 54 10 11)
   (firstPivot 1260 10) := (residualValidities_of_profiles 1260 54 10 11 (by simp)).1
theorem secondValidS111 : ResidualValidity (secondStage 1260 54 10 11)
   (secondPivot 1260 10) := (residualValidities_of_profiles 1260 54 10 11 (by simp)).2
theorem firstValidS110 : ResidualValidity (firstStage 1260 54 0 10)
   (firstPivot 1260 0) := (residualValidities_of_profiles 1260 54 0 10 (by simp)).1
theorem secondValidS110 : ResidualValidity (secondStage 1260 54 0 10)
   (secondPivot 1260 0) := (residualValidities_of_profiles 1260 54 0 10 (by simp)).2
theorem firstValidS101 : ResidualValidity (firstStage 1260 0 10 11)
   (firstPivot 1260 10) := (residualValidities_of_profiles 1260 0 10 11 (by simp)).1
theorem secondValidS101 : ResidualValidity (secondStage 1260 0 10 11)
   (secondPivot 1260 10) := (residualValidities_of_profiles 1260 0 10 11 (by simp)).2
theorem firstValidS100 : ResidualValidity (firstStage 1260 0 0 10)
   (firstPivot 1260 0) := (residualValidities_of_profiles 1260 0 0 10 (by simp)).1
theorem secondValidS100 : ResidualValidity (secondStage 1260 0 0 10)
   (secondPivot 1260 0) := (residualValidities_of_profiles 1260 0 0 10 (by simp)).2
theorem firstValidS011 : ResidualValidity (firstStage 0 54 10 11)
   (firstPivot 0 10) := (residualValidities_of_profiles 0 54 10 11 (by simp)).1
theorem secondValidS011 : ResidualValidity (secondStage 0 54 10 11)
   (secondPivot 0 10) := (residualValidities_of_profiles 0 54 10 11 (by simp)).2
theorem firstValidS010 : ResidualValidity (firstStage 0 54 0 10)
   (firstPivot 0 0) := (residualValidities_of_profiles 0 54 0 10 (by simp)).1
theorem secondValidS010 : ResidualValidity (secondStage 0 54 0 10)
   (secondPivot 0 0) := (residualValidities_of_profiles 0 54 0 10 (by simp)).2
theorem firstValidS001 : ResidualValidity (firstStage 0 0 10 11)
   (firstPivot 0 10) := (residualValidities_of_profiles 0 0 10 11 (by simp)).1
theorem secondValidS001 : ResidualValidity (secondStage 0 0 10 11)
   (secondPivot 0 10) := (residualValidities_of_profiles 0 0 10 11 (by simp)).2
theorem firstValidS000 : ResidualValidity (firstStage 0 0 0 10)
   (firstPivot 0 0) := (residualValidities_of_profiles 0 0 0 10 (by simp)).1
theorem secondValidS000 : ResidualValidity (secondStage 0 0 0 10)
   (secondPivot 0 0) := (residualValidities_of_profiles 0 0 0 10 (by simp)).2
theorem budgetYS111 : rectangleCost 1207 41 10 1260 53 11 12 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1207 41 10 1260 53 11 12 (by simp)
theorem budgetYS110 : rectangleCost 1207 42 9 1260 53 0 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1207 42 9 1260 53 0 11 (by simp)
theorem budgetYS101 : rectangleCost 1208 40 10 1260 0 11 12 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1208 40 10 1260 0 11 12 (by simp)
theorem budgetYS100 : rectangleCost 1208 41 9 1260 0 0 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1208 41 9 1260 0 0 11 (by simp)
theorem budgetYS011 : rectangleCost 1206 41 10 0 53 11 12 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1206 41 10 0 53 11 12 (by simp)
theorem budgetYS010 : rectangleCost 1206 42 9 0 53 0 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1206 42 9 0 53 0 11 (by simp)
theorem budgetYS001 : rectangleCost 1207 40 10 0 0 11 12 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1207 40 10 0 0 11 12 (by simp)
theorem budgetYS000 : rectangleCost 1207 41 9 0 0 0 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1207 41 9 0 0 0 11 (by simp)
theorem budgetS111 : rectangleCost 1206 43 9 1260 54 10 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1206 43 9 1260 54 10 11 (by simp)
theorem budgetS110 : rectangleCost 1206 44 8 1260 54 0 10 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1206 44 8 1260 54 0 10 (by simp)
theorem budgetS101 : rectangleCost 1207 42 9 1260 0 10 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1207 42 9 1260 0 10 11 (by simp)
theorem budgetS100 : rectangleCost 1207 43 8 1260 0 0 10 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1207 43 8 1260 0 0 10 (by simp)
theorem budgetS011 : rectangleCost 1205 43 9 0 54 10 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1205 43 9 0 54 10 11 (by simp)
theorem budgetS010 : rectangleCost 1205 44 8 0 54 0 10 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1205 44 8 0 54 0 10 (by simp)
theorem budgetS001 : rectangleCost 1206 42 9 0 0 10 11 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1206 42 9 0 0 10 11 (by simp)
theorem budgetS000 : rectangleCost 1206 43 8 0 0 0 10 < mcaBudget := by
 exact rectangleCost_lt_of_profiles 1206 43 8 0 0 0 10 (by simp)
end ProximityPrize.SubmissionLower.ContactTwoTailResidualRectangles6734Research

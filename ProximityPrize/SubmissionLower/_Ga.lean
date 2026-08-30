import ProximityPrize.SubmissionLower.GW
namespace ProximityPrize.SubmissionLower.ContactTwoTailRectangleStageBounds6734Research
open ContactFlagBezout6543Research
open ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research
open ContactMovingOuterBudget6719Research
open ContactReducedTaylorProfileResearch
open ContactTwoTailParameters6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
open ContactTwoTailFixedStageBound6734Research
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
theorem fixedStageBound_of_profiles (a b s : ℕ)
   (h :
     (a = 1207 ∧ b = 41 ∧ s = 10) ∨
     (a = 1207 ∧ b = 42 ∧ s = 9) ∨
     (a = 1208 ∧ b = 40 ∧ s = 10) ∨
     (a = 1208 ∧ b = 41 ∧ s = 9) ∨
     (a = 1206 ∧ b = 41 ∧ s = 10) ∨
     (a = 1206 ∧ b = 42 ∧ s = 9) ∨
     (a = 1207 ∧ b = 40 ∧ s = 10) ∨
     (a = 1207 ∧ b = 41 ∧ s = 9) ∨
     (a = 1206 ∧ b = 43 ∧ s = 9) ∨
     (a = 1206 ∧ b = 44 ∧ s = 8) ∨
     (a = 1207 ∧ b = 43 ∧ s = 8) ∨
     (a = 1205 ∧ b = 43 ∧ s = 9) ∨
     (a = 1205 ∧ b = 44 ∧ s = 8) ∨
     (a = 1206 ∧ b = 43 ∧ s = 8)) :
   FixedStageBound a b s := by
 rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
   rcases h with ⟨rfl, rfl, rfl⟩ <;>
   apply fixedStageBound_of_numeric <;> intros <;>
   norm_num [ContactMovingAgreementCertificate6719Research.support,
     ContactProperDelayedTailCertificate6732Research.fixedSupport,
     ContactTwoTailParameters6734Research.n,
     ContactTwoTailParameters6734Research.w,
     ContactTwoTailParameters6734Research.errors,
     ContactTwoTailParameters6734Research.agreements,
     ContactTwoTailParameters6734Research.gap,
     ContactTwoTailParameters6734Research.prime,
     ContactTwoTailFixedSelectedGeneric6734Research.firstTail,
     ContactTwoTailFixedSelectedGeneric6734Research.secondTail,
     ContactTwoTailFixedSelectedGeneric6734Research.fixedFlag,
     ContactReducedTaylorProfileResearch.reducedResidualAgreementFlag,
     ContactReducedTaylorProfileResearch.reducedAgreementDirection,
     ContactIdentityCurveProvider6731Research.identityCurveDegree,
     ContactMovingOuterBudget6719Research.paddedCut,
     ContactMovingPositiveLedger6719Research.centreFlag,
     ContactMovingPositiveLedger6719Research.directionFlag,
     ContactFlagBezout6543Research.flagMixed,
     ContactFlagBezout6543Research.unitZFlag,
     ContactFlagBezout6543Research.unitYZFlag,
     ContactFlagBezout6543Research.add_zOnly,
     ContactFlagBezout6543Research.add_yz,
     ContactFlagBezout6543Research.add_all,
     ContactFlagBezout6543Research.nsmul_zOnly,
     ContactFlagBezout6543Research.nsmul_yz,
     ContactFlagBezout6543Research.nsmul_all] at * <;> omega
theorem stageBoundYS111 : FixedStageBound 1207 41 10 := by
 exact fixedStageBound_of_profiles 1207 41 10 (by simp)
theorem stageBoundYS110 : FixedStageBound 1207 42 9 := by
 exact fixedStageBound_of_profiles 1207 42 9 (by simp)
theorem stageBoundYS101 : FixedStageBound 1208 40 10 := by
 exact fixedStageBound_of_profiles 1208 40 10 (by simp)
theorem stageBoundYS100 : FixedStageBound 1208 41 9 := by
 exact fixedStageBound_of_profiles 1208 41 9 (by simp)
theorem stageBoundYS011 : FixedStageBound 1206 41 10 := by
 exact fixedStageBound_of_profiles 1206 41 10 (by simp)
theorem stageBoundYS010 : FixedStageBound 1206 42 9 := by
 exact fixedStageBound_of_profiles 1206 42 9 (by simp)
theorem stageBoundYS001 : FixedStageBound 1207 40 10 := by
 exact fixedStageBound_of_profiles 1207 40 10 (by simp)
theorem stageBoundYS000 : FixedStageBound 1207 41 9 := by
 exact fixedStageBound_of_profiles 1207 41 9 (by simp)
theorem stageBoundS111 : FixedStageBound 1206 43 9 := by
 exact fixedStageBound_of_profiles 1206 43 9 (by simp)
theorem stageBoundS110 : FixedStageBound 1206 44 8 := by
 exact fixedStageBound_of_profiles 1206 44 8 (by simp)
theorem stageBoundS101 : FixedStageBound 1207 42 9 :=
 stageBoundYS110
theorem stageBoundS100 : FixedStageBound 1207 43 8 := by
 exact fixedStageBound_of_profiles 1207 43 8 (by simp)
theorem stageBoundS011 : FixedStageBound 1205 43 9 := by
 exact fixedStageBound_of_profiles 1205 43 9 (by simp)
theorem stageBoundS010 : FixedStageBound 1205 44 8 := by
 exact fixedStageBound_of_profiles 1205 44 8 (by simp)
theorem stageBoundS001 : FixedStageBound 1206 42 9 :=
 stageBoundYS010
theorem stageBoundS000 : FixedStageBound 1206 43 8 := by
 exact fixedStageBound_of_profiles 1206 43 8 (by simp)
end ProximityPrize.SubmissionLower.ContactTwoTailRectangleStageBounds6734Research

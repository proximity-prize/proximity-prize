import ProximityPrize.SubmissionLower.BCHKSFrobeniusHighSupportMaxRank6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusMomentRecoveryBoundary6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
def firstHighSupport6401 : Nat := 65537
def residualDegreeFromSupport6401 (s : Nat) : Nat :=
  s - firstHighSupport6401
theorem residualDegreeFromSupport_eq6401
    (s r : Nat) (hs : s = firstHighSupport6401 + r) :
    residualDegreeFromSupport6401 s = r := by
  simp [residualDegreeFromSupport6401, firstHighSupport6401, hs]
theorem momentDeficit_eq6401
    (s r h : Nat) (hs : s = firstHighSupport6401 + r) :
    (2 * s - 1) - (keyRedundancy6401 + h) =
      (2 * r + 1) - h := by
  norm_num [firstHighSupport6401, keyRedundancy6401, n6401,
    ownerDegreeCap6401] at hs ⊢
  omega
theorem longMomentWindow_iff_excess_gt_twiceResidual6401
    (s r h : Nat) (hs : s = firstHighSupport6401 + r) :
    2 * s - 1 ≤ keyRedundancy6401 + h ↔ 2 * r + 1 ≤ h := by
  norm_num [firstHighSupport6401, keyRedundancy6401, n6401,
    ownerDegreeCap6401] at hs ⊢
  omega
theorem shortMomentWindow_iff_excess_le_twiceResidual6401
    (s r h : Nat) (hs : s = firstHighSupport6401 + r) :
    keyRedundancy6401 + h < 2 * s - 1 ↔ h ≤ 2 * r := by
  norm_num [firstHighSupport6401, keyRedundancy6401, n6401,
    ownerDegreeCap6401] at hs ⊢
  omega
theorem longMomentWindow_iff_rankNullity6401
    (s h delta : Nat)
    (hs : s = keyFirstLaneRows6401 + h + delta)
    (hhigh : firstHighSupport6401 ≤ s) :
    2 * s - 1 ≤ keyRedundancy6401 + h ↔
      h + 2 * delta ≤ 22509 := by
  norm_num [firstHighSupport6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401, bchksErrors6401,
    n6401, ownerDegreeCap6401] at hs hhigh ⊢
  omega
theorem shortMomentWindow_iff_rankNullity6401
    (s h delta : Nat)
    (hs : s = keyFirstLaneRows6401 + h + delta)
    (hhigh : firstHighSupport6401 ≤ s) :
    keyRedundancy6401 + h < 2 * s - 1 ↔
      22510 ≤ h + 2 * delta := by
  norm_num [firstHighSupport6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401, bchksErrors6401,
    n6401, ownerDegreeCap6401] at hs hhigh ⊢
  omega
theorem residualDegree_window6401
    (s : Nat) (hlo : firstHighSupport6401 ≤ s)
    (hhi : s ≤ keyErrors6401) :
    residualDegreeFromSupport6401 s ≤ 11253 := by
  norm_num [residualDegreeFromSupport6401, firstHighSupport6401,
    keyErrors6401, bchksErrors6401, keyRedundancy6401, n6401,
    ownerDegreeCap6401] at hlo hhi ⊢
  omega
end BCHKSFrobeniusMomentRecoveryBoundary6401
end ProximityPrize.SubmissionLower

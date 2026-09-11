import ProximityPrize.SubmissionLower.PartG059


section Compact_SecondJetIdentity
/-! The identity-tail branch at 80791 errors is covered by the normal C2
cost alone. These are polynomial identities over naturals, with all slack
coefficients nonnegative. -/
namespace ProximityPrize.SubmissionLower.SecondJetIdentity
open RCN146 RCN086 RCN095 RCN198 RCN206 RCN263 RCN327 LocatorHybridCells LocatorHybridCellsC1
open Lower80788.HybridIdentityC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
def slackZ (a b s : ℕ) : ℕ :=
    3426347998358554 +
    7590254516834724*s +
    1727702726868992*s^2 +
    5183147723980800*b +
    3455405453737984*b*s

def slackYZ (a b s : ℕ) : ℕ :=
    6852557594657314 +
    11725031083645556*s +
    1727702726868992*s^2 +
    5183147723980800*b +
    3455405453737984*b*s +
    5183147723980800*a +
    3455405453737984*a*s

def slackAll (a b s : ℕ) : ℕ :=
    6794111748069970 +
    11725031083645556*s +
    1727702726868992*s^2 +
    11725031083645556*b +
    3455405453737984*b*s +
    1727702726868992*b^2 +
    7590254516834724*a +
    3455405453737984*a*s +
    3455405453737984*a*b

theorem identity_normal_exact (flag : FlagDegree) (a b s : ℕ) :
    50282*flagMixed flag (reducedABS (a+2) (b+1) (s+1)) (rationalABS (a+2) (b+1) (s+1)) =
      131073*80792*identityCurveDegree flag (a+2) (b+1) (s+1) 131071+
      flag.zOnly*slackZ a b s+flag.yz*slackYZ a b s+flag.all*slackAll a b s := by
  have hid := identityDegree_linear flag (a+2) (b+1) (s+1)
  change identityCurveDegree flag (a+2) (b+1) (s+1) 131071 = _ at hid
  rw [hid]
  norm_num [reducedABS,rationalABS,slackZ,slackYZ,slackAll,flagMixed]
  ring

theorem identity_le_normal_abs (flag : FlagDegree) (a b s : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hs : 1 ≤ s) :
    131073*80792*identityCurveDegree flag a b s 131071 ≤
      50282*flagMixed flag (reducedABS a b s) (rationalABS a b s) := by
  obtain ⟨a,rfl⟩ : ∃ a', a = a'+2 := ⟨a-2,by omega⟩
  obtain ⟨b,rfl⟩ : ∃ b', b = b'+1 := ⟨b-1,by omega⟩
  obtain ⟨s,rfl⟩ : ∃ s', s = s'+1 := ⟨s-1,by omega⟩
  rw [identity_normal_exact]
  omega

theorem cell_first_eq (t y r : ℕ) :
    cellFirstTail t y r = reducedABS (cellA t y) (cellB y r) (cellS r) := by
  unfold cellFirstTail cellSupport
  rw [Lower80788.FixedStage.tail_support_formula]
  simp only [RCN327.w,reducedABS]
  congr 1 <;> ring

theorem cell_normal_eq (t y r : ℕ) :
    cellHybridCoordinateC1 t y r = rationalABS (cellA t y) (cellB y r) (cellS r) := by
  simp only [cellHybridCoordinateC1,cellRational,cellDirection,directionFlag,rationalABS,RCN327.w]
  congr 1 <;> ring

theorem identity_le_normal (flag : FlagDegree) (t y r : ℕ)
    (ha : y+2 ≤ t) (hb : r+2 ≤ y) (hr : 3 ≤ r) :
    131073*80792*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) 131071 ≤
      50282*flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r) := by
  rw [cell_first_eq,cell_normal_eq]
  apply identity_le_normal_abs
  · dsimp [cellA]; omega
  · dsimp [cellB]; omega
  · dsimp [cellS]; omega

end
end ProximityPrize.SubmissionLower.SecondJetIdentity

end Compact_SecondJetIdentity

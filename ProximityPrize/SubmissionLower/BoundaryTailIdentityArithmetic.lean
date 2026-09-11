import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

open RCN095 RCN146
open Lower80788.FixedStage
open Lower80788.HybridIdentityC2

def newNormal (f : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed f (reducedABS a b s)
    (rationalABS a b s + 131071 • unitAllFlag)

def newCost (f : FlagDegree) (a b s : ℕ) : ℕ :=
  newNormal f a b s + 65539 * flagMixed f (mfibABS a b s) (mcutABS a b s)

def slackGeneric (f : FlagDegree) (a b s : ℕ) : ℕ :=
  f.zOnly * (21554512223976792 + 9930474304039194*b + 14061926840885886*s + 2158789166144004*s^2 + 4317578332288008*b*s) +
    f.yz * (14612708359181052 + 9930474304039194*a + 9930474304039194*b + 11285205294967590*s + 2158789166144004*s^2 + 4317578332288008*a*s + 4317578332288008*b*s) +
    f.all * (11463707449896708 + 14061926840885886*a + 11285205294967590*b + 2158789166144004*b^2 + 11285205294967590*s + 2158789166144004*s^2 + 4317578332288008*a*b + 4317578332288008*a*s + 4317578332288008*b*s)

def slackNormal (f : FlagDegree) (a b s : ℕ) : ℕ :=
  f.zOnly * (10328417230972668 + 6908062086463488*b + 9312420045197652*s + 1727015521615872*s^2 + 3454031043231744*b*s) +
    f.yz * (17202737539103904 + 6908062086463488*a + 6908062086463488*b + 13443760585742844*s + 1727015521615872*s^2 + 3454031043231744*a*s + 3454031043231744*b*s) +
    f.all * (17135357969175360 + 9312420045197652*a + 13443760585742844*b + 1727015521615872*b^2 + 13443760585742844*s + 1727015521615872*s^2 + 3454031043231744*a*b + 3454031043231744*a*s + 3454031043231744*b*s)

theorem generic_slack_identity (f : FlagDegree) (a b s : ℕ) :
    50262 * newCost f a (b+1) (s+1) =
        131073 * 80812 * identityCurveDegree f a (b+1) (s+1) 131071 +
      slackGeneric f a b s := by
  change 50262 * newCost f a (b+1) (s+1) =
    131073 * 80812 * identityCurveDegree f a (b+1) (s+1)
      Lower80788.HybridIdentityC2.w + slackGeneric f a b s
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newCost, newNormal, slackGeneric, reducedABS, rationalABS,
    mfibABS, mcutABS, flagMixed, unitAllFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem normal_slack_identity (f : FlagDegree) (a b s : ℕ) :
    50262 * newNormal f (a+2) (b+1) (s+1) =
        131073 * 80812 * identityCurveDegree f (a+2) (b+1) (s+1) 131071 +
      slackNormal f a b s := by
  change 50262 * newNormal f (a+2) (b+1) (s+1) =
    131073 * 80812 * identityCurveDegree f (a+2) (b+1) (s+1)
      Lower80788.HybridIdentityC2.w + slackNormal f a b s
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newNormal, slackNormal, reducedABS, rationalABS, flagMixed,
    unitAllFlag, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz,
    nsmul_all]
  ring

theorem generic_absorption (f : FlagDegree) (a b s : ℕ) (hb : 0 ≤ a)
    (hb' : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 80812 * identityCurveDegree f a b s 131071 ≤
      50262 * newCost f a b s := by
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb'
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
  have h := generic_slack_identity f a b' s'
  have heq : 50262 * newCost f a (1+b') (1+s') =
      131073 * 80812 * identityCurveDegree f a (1+b') (1+s')
        Lower80788.HybridIdentityC2.w + slackGeneric f a b' s' := by
    simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w] using
    (show 131073 * 80812 * identityCurveDegree f a (1+b') (1+s')
        Lower80788.HybridIdentityC2.w ≤
      50262 * newCost f a (1+b') (1+s') by
      calc
        _ ≤ _ + slackGeneric f a b' s' := Nat.le_add_right _ _
        _ = _ := heq.symm)

theorem normal_absorption (f : FlagDegree) (a b s : ℕ) (ha : 2 ≤ a)
    (hb : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 80812 * identityCurveDegree f a b s 131071 ≤
      50262 * newNormal f a b s := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
  have h := normal_slack_identity f a' b' s'
  have heq : 50262 * newNormal f (2+a') (1+b') (1+s') =
      131073 * 80812 * identityCurveDegree f (2+a') (1+b') (1+s')
        Lower80788.HybridIdentityC2.w + slackNormal f a' b' s' := by
    simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w] using
    (show 131073 * 80812 * identityCurveDegree f (2+a') (1+b') (1+s')
        Lower80788.HybridIdentityC2.w ≤
      50262 * newNormal f (2+a') (1+b') (1+s') by
      calc
        _ ≤ _ + slackNormal f a' b' s' := Nat.le_add_right _ _
        _ = _ := heq.symm)

end ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

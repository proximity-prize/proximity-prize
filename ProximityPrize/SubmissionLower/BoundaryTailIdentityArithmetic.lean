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
  f.zOnly * (21561040785294102 + 9932450046012064*b +
      2159218673359424*s^2 + 14065620618274076*s + 4318437346718848*b*s) +
    f.yz * (14620095927064812 + 9932450046012064*a + 9932450046012064*b +
      2159218673359424*s^2 + 11289242674982360*s +
      4318437346718848*a*s + 4318437346718848*b*s) +
    f.all * (11473156663686748 + 14065620618274076*a +
      2159218673359424*b^2 + 11289242674982360*b + 2159218673359424*s^2 +
      11289242674982360*s + 4318437346718848*a*b +
      4318437346718848*a*s + 4318437346718848*b*s)

def slackNormal (f : FlagDegree) (a b s : ℕ) : ℕ :=
  f.zOnly * (10332712276911958 + 6909436496969728*b +
      1727359124242432*s^2 + 9315168872763772*s + 3454718248484864*b*s) +
    f.yz * (17210640412622124 + 6909436496969728*a + 6909436496969728*b +
      1727359124242432*s^2 + 13448227426441784*s +
      3454718248484864*a*s + 3454718248484864*b*s) +
    f.all * (17147727704364180 + 9315168872763772*a +
      1727359124242432*b^2 + 13448227426441784*b + 1727359124242432*s^2 +
      13448227426441784*s + 3454718248484864*a*b +
      3454718248484864*a*s + 3454718248484864*b*s)

theorem generic_slack_identity (f : FlagDegree) (a b s : ℕ) :
    50272 * newCost f a (b+1) (s+1) =
        131073 * 80802 * identityCurveDegree f a (b+1) (s+1) 131071 +
      slackGeneric f a b s := by
  change 50272 * newCost f a (b+1) (s+1) =
    131073 * 80802 * identityCurveDegree f a (b+1) (s+1)
      Lower80788.HybridIdentityC2.w + slackGeneric f a b s
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newCost, newNormal, slackGeneric, reducedABS, rationalABS,
    mfibABS, mcutABS, flagMixed, unitAllFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem normal_slack_identity (f : FlagDegree) (a b s : ℕ) :
    50272 * newNormal f (a+2) (b+1) (s+1) =
        131073 * 80802 * identityCurveDegree f (a+2) (b+1) (s+1) 131071 +
      slackNormal f a b s := by
  change 50272 * newNormal f (a+2) (b+1) (s+1) =
    131073 * 80802 * identityCurveDegree f (a+2) (b+1) (s+1)
      Lower80788.HybridIdentityC2.w + slackNormal f a b s
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newNormal, slackNormal, reducedABS, rationalABS, flagMixed,
    unitAllFlag, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz,
    nsmul_all]
  ring

theorem generic_absorption (f : FlagDegree) (a b s : ℕ) (hb : 0 ≤ a)
    (hb' : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 80802 * identityCurveDegree f a b s 131071 ≤
      50272 * newCost f a b s := by
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb'
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
  have h := generic_slack_identity f a b' s'
  have heq : 50272 * newCost f a (1+b') (1+s') =
      131073 * 80802 * identityCurveDegree f a (1+b') (1+s')
        Lower80788.HybridIdentityC2.w + slackGeneric f a b' s' := by
    simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w] using
    (show 131073 * 80802 * identityCurveDegree f a (1+b') (1+s')
        Lower80788.HybridIdentityC2.w ≤
      50272 * newCost f a (1+b') (1+s') by
      calc
        _ ≤ _ + slackGeneric f a b' s' := Nat.le_add_right _ _
        _ = _ := heq.symm)

theorem normal_absorption (f : FlagDegree) (a b s : ℕ) (ha : 2 ≤ a)
    (hb : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 80802 * identityCurveDegree f a b s 131071 ≤
      50272 * newNormal f a b s := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
  have h := normal_slack_identity f a' b' s'
  have heq : 50272 * newNormal f (2+a') (1+b') (1+s') =
      131073 * 80802 * identityCurveDegree f (2+a') (1+b') (1+s')
        Lower80788.HybridIdentityC2.w + slackNormal f a' b' s' := by
    simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simpa [Lower80788.HybridIdentityC2.w, Lower80788.FixedStage.w] using
    (show 131073 * 80802 * identityCurveDegree f (2+a') (1+b') (1+s')
        Lower80788.HybridIdentityC2.w ≤
      50272 * newNormal f (2+a') (1+b') (1+s') by
      calc
        _ ≤ _ + slackNormal f a' b' s' := Nat.le_add_right _ _
        _ = _ := heq.symm)

end ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

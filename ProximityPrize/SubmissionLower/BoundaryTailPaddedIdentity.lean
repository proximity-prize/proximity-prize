import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailPaddedIdentity

open RCN095 RCN146
open Lower80788.FixedStage

set_option maxHeartbeats 1000000

def slackZ (b s : ℕ) : ℕ :=
  6199535116604890 + 6909383782957056*b + 11042415979729276*s +
    3454691891478528*s^2 + 6909383782957056*b*s

def slackYZ (a b s : ℕ) : ℕ :=
  2034968201667316 + 6909383782957056*a + 6909383782957056*b +
    8266038036437560*s + 3454691891478528*s^2 +
    6909383782957056*a*s + 6909383782957056*b*s

def slackAll (a b s : ℕ) : ℕ :=
  2713287325090188 + 11042415979729276*a + 8266038036437560*b +
    8266038036437560*s + 3454691891478528*b^2 + 3454691891478528*s^2 +
    6909383782957056*a*b + 6909383782957056*a*s + 6909383782957056*b*s

/-- The ordinary two-tail identity budget at 80801 errors. The ABS parameters
are unshifted, so this includes the padded boundary cases b=0 and s=0. -/
theorem identity_budget_exact (f : FlagDegree) (a b s : ℕ) :
    50272 * flagMixed f (firstTail a b s) (secondTail a b s) =
      131073 * 80802 * identityCurveDegree f a b s 131071 +
        (f.zOnly * slackZ b s + f.yz * slackYZ a b s + f.all * slackAll a b s) := by
  change 50272 * flagMixed f (firstTail a b s) (secondTail a b s) =
    131073 * 80802 * identityCurveDegree f a b s Lower80788.FixedStage.w +
      (f.zOnly * slackZ b s + f.yz * slackYZ a b s + f.all * slackAll a b s)
  rw [Lower80788.FixedStage.identityDegree_linear]
  norm_num [firstTail, secondTail, Lower80788.FixedStage.tail_support_formula,
    Lower80788.FixedStage.w, flagMixed, slackZ, slackYZ, slackAll]
  ring

theorem identity_absorption (f : FlagDegree) (a b s : ℕ) :
    131073 * 80802 * identityCurveDegree f a b s 131071 ≤
      50272 * flagMixed f (firstTail a b s) (secondTail a b s) := by
  rw [identity_budget_exact]
  exact Nat.le_add_right _ _

theorem low_pad_parameters (p : FlagDegree)
    (h : ¬ LocatorHybridCostC2.HybridAppliesC2 p) :
    Lower80788.Fixed.padSlope p = 0 ∨ Lower80788.Fixed.padB p = 0 := by
  dsimp [LocatorHybridCostC2.HybridAppliesC2, LocatorFactorAggregate.middle] at h
  dsimp [Lower80788.Fixed.padSlope, Lower80788.Fixed.padB,
    LocatorFactorAggregate.padS, LocatorFactorAggregate.padY,
    LocatorFactorAggregate.middle]
  omega

/-- On a non-hybrid padded cell either the padded R degree is 2 (s=0),
or the padded YR degree is the R degree plus 1 (b=0). The old rectangular
gate is already small on both parts of this boundary. -/
theorem low_provider_mixed_gate (b s : ℕ) (f : FlagDegree)
    (hS : s+2 ≤ 30) (hY : b+s+3 ≤ 139)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131072*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-2)*131072) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 276 := by omega
    have hs : 2*(s+2)-2 ≤ 2 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 139 := by omega
    calc
      _ ≤ (1+131072*276)*2 + 139*(2*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 60 := by omega
    have hs : 2*(s+2)-2 ≤ 58 := by omega
    have hfS : f.all ≤ 30 := by omega
    have hfY : f.yz+f.all ≤ 31 := by omega
    calc
      _ ≤ (1+131072*60)*30 + 31*(58*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide

theorem low_identity_mixed_gate (b s : ℕ) (f : FlagDegree)
    (hS : s+2 ≤ 30) (hY : b+s+3 ≤ 139)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131071*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-1)*131071) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 276 := by omega
    have hs : 2*(s+2)-1 ≤ 3 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 139 := by omega
    calc
      _ ≤ (1+131071*276)*2 + 139*(3*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 60 := by omega
    have hs : 2*(s+2)-1 ≤ 59 := by omega
    have hfS : f.all ≤ 30 := by omega
    have hfY : f.yz+f.all ≤ 31 := by omega
    calc
      _ ≤ (1+131071*60)*30 + 31*(59*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide

end ProximityPrize.SubmissionLower.BoundaryTailPaddedIdentity

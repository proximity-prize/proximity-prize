import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailPaddedIdentity

open RCN095 RCN146
open Lower80788.FixedStage

set_option maxHeartbeats 1000000

def slackZ (b s : ℕ) : ℕ :=
  6196958107391400 + 6908009382936576*b + 11039323571818836*s + 3454004691468288*s^2 + 6908009382936576*b*s

def slackYZ (a b s : ℕ) : ℕ :=
  2031875788513956 + 6908009382936576*a + 6908009382936576*b + 8262602025900540*s + 3454004691468288*s^2 + 6908009382936576*a*s + 6908009382936576*b*s

def slackAll (a b s : ℕ) : ℕ :=
  2709164101435638 + 11039323571818836*a + 8262602025900540*b + 3454004691468288*b^2 + 8262602025900540*s + 3454004691468288*s^2 + 6908009382936576*a*b + 6908009382936576*a*s + 6908009382936576*b*s

/-- The ordinary two-tail identity budget at 80811 errors. The ABS parameters
are unshifted, so this includes the padded boundary cases b=0 and s=0. -/
theorem identity_budget_exact (f : FlagDegree) (a b s : ℕ) :
    50262 * flagMixed f (firstTail a b s) (secondTail a b s) =
      131073 * 80812 * identityCurveDegree f a b s 131071 +
        (f.zOnly * slackZ b s + f.yz * slackYZ a b s + f.all * slackAll a b s) := by
  change 50262 * flagMixed f (firstTail a b s) (secondTail a b s) =
    131073 * 80812 * identityCurveDegree f a b s Lower80788.FixedStage.w +
      (f.zOnly * slackZ b s + f.yz * slackYZ a b s + f.all * slackAll a b s)
  rw [Lower80788.FixedStage.identityDegree_linear]
  norm_num [firstTail, secondTail, Lower80788.FixedStage.tail_support_formula,
    Lower80788.FixedStage.w, flagMixed, slackZ, slackYZ, slackAll]
  ring

theorem identity_absorption (f : FlagDegree) (a b s : ℕ) :
    131073 * 80812 * identityCurveDegree f a b s 131071 ≤
      50262 * flagMixed f (firstTail a b s) (secondTail a b s) := by
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
    (hS : s+2 ≤ 31) (hY : b+s+3 ≤ 142)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131072*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-2)*131072) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 282 := by omega
    have hs : 2*(s+2)-2 ≤ 2 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 142 := by omega
    calc
      _ ≤ (1+131072*282)*2 + 142*(2*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 62 := by omega
    have hs : 2*(s+2)-2 ≤ 60 := by omega
    have hfS : f.all ≤ 31 := by omega
    have hfY : f.yz+f.all ≤ 32 := by omega
    calc
      _ ≤ (1+131072*62)*31 + 32*(60*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide

theorem low_identity_mixed_gate (b s : ℕ) (f : FlagDegree)
    (hS : s+2 ≤ 31) (hY : b+s+3 ≤ 142)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131071*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-1)*131071) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 282 := by omega
    have hs : 2*(s+2)-1 ≤ 3 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 142 := by omega
    calc
      _ ≤ (1+131071*282)*2 + 142*(3*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 62 := by omega
    have hs : 2*(s+2)-1 ≤ 61 := by omega
    have hfS : f.all ≤ 31 := by omega
    have hfY : f.yz+f.all ≤ 32 := by omega
    calc
      _ ≤ (1+131071*62)*31 + 32*(61*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide

end ProximityPrize.SubmissionLower.BoundaryTailPaddedIdentity

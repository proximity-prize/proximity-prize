import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.MovingFiberPaddedIdentity6811

open RCN095 RCN149
open Lower80788.FixedStage

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem identity_absorption (f : FlagDegree) (a b s : ℕ) :
    131073 * 80880 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s 131071 ≤
      50194 * flagMixed f (firstTail a b s) (secondTail a b s) := by
  change 131073 * 80880 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s Lower80788.FixedStage.w ≤ _
  rw [Lower80788.FixedStage.identityDegree_linear]
  norm_num [firstTail, secondTail, Lower80788.FixedStage.tail_support_formula,
    Lower80788.FixedStage.w, flagMixed]
  ring_nf
  omega

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
    (hS : s+2 ≤ 32) (hY : b+s+3 ≤ 149)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131072*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-2)*131072) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 296 := by omega
    have hs : 2*(s+2)-2 ≤ 2 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 149 := by omega
    calc
      _ ≤ (1+131072*296)*2 + 149*(2*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 64 := by omega
    have hs : 2*(s+2)-2 ≤ 62 := by omega
    have hfS : f.all ≤ 32 := by omega
    have hfY : f.yz+f.all ≤ 33 := by omega
    calc
      _ ≤ (1+131072*64)*32 + 33*(62*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide

theorem low_identity_mixed_gate (b s : ℕ) (f : FlagDegree)
    (hS : s+2 ≤ 32) (hY : b+s+3 ≤ 149)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131071*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-1)*131071) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 296 := by omega
    have hs : 2*(s+2)-1 ≤ 3 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 149 := by omega
    calc
      _ ≤ (1+131071*296)*2 + 149*(3*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 64 := by omega
    have hs : 2*(s+2)-1 ≤ 63 := by omega
    have hfS : f.all ≤ 32 := by omega
    have hfY : f.yz+f.all ≤ 33 := by omega
    calc
      _ ≤ (1+131071*64)*32 + 33*(63*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide

end ProximityPrize.SubmissionLower.MovingFiberPaddedIdentity6811
